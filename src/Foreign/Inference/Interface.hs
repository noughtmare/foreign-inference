{-# LANGUAGE ExistentialQuantification, DeriveDataTypeable #-}
{-# LANGUAGE TemplateHaskell, StandaloneDeriving, ViewPatterns, CPP #-}
{-# LANGUAGE FlexibleContexts #-}
-- | This module defines an external representation of library
-- interfaces.  Individual libraries are represented by the
-- 'LibraryInterface'.  The analysis reads these in and writes these
-- out.
--
-- During the analysis, the dependencies of the current library are
-- represented using the 'DependencySummary', which is composed of
-- several 'LibraryInterface's.
--
-- Note that this module does not currently handle by-value structs
-- properly.  The various LLVM frontends lower these according to the
-- target ABI and it is a bit difficult to map the result exactly back
-- to how it appeared in the source.  This will have to be done with
-- some metadata.
module Foreign.Inference.Interface (
  -- * Classes
  SummarizeModule(..),
  ModuleSummary(..),
  HasDependencies(..),
  -- * Types
  Witness(..),
  DependencySummary(manualAnnotations),
  LibraryInterface(..),
  ManualAnnotations,
  ForeignFunction(..),
  Parameter(..),
  CEnum(..),
  CType(..),
  Linkage(..),
  ErrorAction(..),
  ErrorActionArgument(..),
  ErrorReturn(..),
  ParamAnnotation(..),
  StructFieldAnnotation(..),
  FuncAnnotation(..),
  TypeAnnotation(..),
  ModuleAnnotation(..),
  StdLib(..),
  -- * Functions
  lookupArgumentSummary,
  lookupArgumentSummaryList,
  lookupStructFieldSummary,
  lookupStructFieldSummaryList,
  lookupFunctionSummary,
  lookupFunctionSummaryList,
  loadDependencies,
  loadDependencies',
  moduleToLibraryInterface,
  saveInterface,
  saveModule,
  readLibraryInterface,
  addManualAnnotations,
  loadAnnotations,
  refCountFunctionsForField,
  isRefCountedObject,
  -- *
  userFunctionAnnotations,
  userParameterAnnotations
  ) where

import GHC.Conc ( getNumCapabilities )

import Control.Arrow
import Control.Concurrent.ParallelIO.Local
import Control.DeepSeq
import Control.Exception as E
import Control.Monad ( liftM )
import Control.Monad.Writer.Class ( MonadWriter )
import Data.Aeson (decode', encode)
import qualified Data.ByteString.Char8 as SBS
import qualified Data.ByteString.Lazy as LBS
import Data.Data
import Data.FileEmbed
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as M
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Text ( Text )
import qualified Data.Text as T
import Data.Foldable ( foldl' )
import Debug.Trace.LocationTH
import System.FilePath
import System.IO.Error
import Text.Jasmine

import qualified LLVM.Analysis as LLVM
import LLVM.Analysis hiding (Linkage)
import LLVM.Analysis.AccessPath

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface.Metadata
import Foreign.Inference.Interface.Types





import Data.List ( stripPrefix )
import Paths_foreign_inference

import Debug.Trace
debug = flip trace

getStaticFiles :: IO (HashMap FilePath SBS.ByteString)
getStaticFiles = do
  statDir <- getDataDir
  dat <- getDir statDir
  let strip' p = fromMaybe p (stripPrefix "stdlibs/" p)
  return $ M.fromList (map (first strip') dat)


-- import Debug.Trace
-- debug = flip trace

-- | The extension used for all summaries
summaryExtension :: String
summaryExtension = "json"


data InterfaceException = DependencyMissing FilePath
                        | DependencyDecodeError FilePath
                        deriving (Show, Typeable)
instance Exception InterfaceException


type ManualAnnotations = Map String ([FuncAnnotation], IntMap [ParamAnnotation])
type DepMap = HashMap String ForeignFunction

-- | This index is a map from struct fields containing ref-counting
-- finalizers to the associated ref/unref functions.
type RefCountIndex = Map (String, [AccessType]) (String, String)
type RefCountSuperclassIndex = Map String (String, String)

-- | A summary of all of the functions that are dependencies of the
-- current library.
data DependencySummary =
  DependencySummary { depSummary :: DepMap
                    , manualAnnotations :: ManualAnnotations
                    , refCountIndex :: RefCountIndex -- ^ The access paths that denote ref counted objects
                    , refCountSuperclasses :: RefCountSuperclassIndex -- ^ Ref counted objects that can be identified via structural subtyping
                    }
  deriving (Show)

-- | Determine if the given Type is ref counted.  Any non-struct type
-- will return False.
isRefCountedObject :: DependencySummary -> Type -> Maybe (String, String)
isRefCountedObject ds t =
  case t of
    Struct (Right (Ident n)) _ _ ->
      Map.lookup (structBaseName n) (refCountSuperclasses ds)
    _ -> Nothing

refCountFunctionsForField :: DependencySummary -> AbstractAccessPath -> Maybe (String, String)
refCountFunctionsForField ds accPath = do
  extPath <- externalizeAccessPath accPath
  Map.lookup extPath (refCountIndex ds)

indexRefCounts :: DepMap -> RefCountIndex
indexRefCounts = foldr indexForeignFunction mempty . M.elems
  where
    unrefDetails (PAUnref refFunc fields _) = Just (refFunc, fields)
    unrefDetails _ = Nothing
    -- | Only want to index the unref functions with a single argument
    -- (otherwise we can't automatially call them anyway).
    indexForeignFunction ff acc =
      case foreignFunctionParameters ff of
        [p] ->
          case mapMaybe unrefDetails (parameterAnnotations p) of
            [(refFunc, fields)] ->
              foldl' (\a f -> Map.insert f (refFunc, foreignFunctionName ff) a) acc fields
            _ -> acc
        _ -> acc

indexStructuralSuperclasses :: DepMap -> RefCountSuperclassIndex
indexStructuralSuperclasses = foldr indexForeignFunction mempty . M.elems
  where
    unrefDetails (PAUnref refFunc _ superclasses) = Just (refFunc, superclasses)
    unrefDetails _ = Nothing

    indexForeignFunction ff acc =
      case foreignFunctionParameters ff of
        [p] ->
          case mapMaybe unrefDetails (parameterAnnotations p) of
            [(refFunc, types)] ->
              foldl' (\a t -> Map.insert t (refFunc, foreignFunctionName ff) a) acc types
            _ -> acc
        _ -> acc

-- | Take input annotations and add them to the known annotations in a
-- dependency summary.
addManualAnnotations :: DependencySummary -> ManualAnnotations -> DependencySummary
addManualAnnotations ds as =
  ds { manualAnnotations = manualAnnotations ds `mappend` as }

-- | The standard library summaries that can be automatically loaded
-- by 'loadDependencies''.
data StdLib = CStdLib
            | CxxStdLib
            | LLVMLib
            deriving (Show)

-- | A witness is an instruction and a (short) free-form string
-- describing what was witnessed on that line.
--
-- The file name is not included because the file is identified by the
-- enclosing function of the Argument.
--
-- WARNING: Don't put anything javascript-unsafe in the String.  This
-- could be enforced but doesn't seem worth the effort right now.
data Witness = Witness !Stmt String
             deriving (Eq, Ord, Show)

instance NFData Witness where
  rnf w@(Witness _ s) = s `deepseq` w `seq` ()

-- | An existential wrapper around types implementing
-- 'SummarizeModule' to allow heterogenous lists of analysis results.
data ModuleSummary = forall a . (SummarizeModule a) => ModuleSummary a

-- | An interface for analyses to implement in order to annotate
-- constructs in 'Module's.
class SummarizeModule s where
  summarizeArgument :: Argument -> s -> [(ParamAnnotation, [Witness])]
  summarizeFunction :: Define -> s -> [(FuncAnnotation, [Witness])]
  -- | Annotate types.  The default implementation just returns the
  -- empty list
  summarizeType :: CType -> s -> [(TypeAnnotation, [Witness])]
  summarizeType _ _ = []
  summarizeModule :: Module -> s -> [ModuleAnnotation]
  summarizeModule _ _ = []
  summarizeStructField :: String -> Integer -> s -> [(StructFieldAnnotation, [Witness])]
  summarizeStructField _ _ _ = []

instance SummarizeModule ModuleSummary where
  summarizeArgument a (ModuleSummary s) = summarizeArgument a s
  summarizeFunction f (ModuleSummary s) = summarizeFunction f s
  summarizeType t (ModuleSummary s) = summarizeType t s
  summarizeModule m (ModuleSummary s) = summarizeModule m s
  summarizeStructField t f (ModuleSummary s) = summarizeStructField t f s

-- | Persist a 'LibraryInterface' to disk in the given @summaryDir@.
-- It uses the name specified in the 'LibraryInterface' to choose the
-- filename.
--
-- > saveInterface summaryDir iface
saveInterface :: FilePath -> LibraryInterface -> IO ()
saveInterface summaryDir i = do
  let bs = encode i
      path = summaryDir </> libraryName i <.> summaryExtension
  LBS.writeFile path bs

-- | A shortcut to convert a 'Module' into a 'LibraryInterface' and
-- then persist it as in 'saveInterface'.
saveModule :: FilePath -> String -> [String] -> Module -> [ModuleSummary] -> DependencySummary -> IO ()
saveModule summaryDir name deps m summaries ds = do
  let i = moduleToLibraryInterface m name deps summaries (manualAnnotations ds)
  saveInterface summaryDir i

-- | Load annotations supplied by the user.  Annotations are just a
-- JSON encoding of the LibraryAnnotations type.
loadAnnotations :: FilePath -> IO ManualAnnotations
loadAnnotations p = do
  c <- LBS.readFile p
  case decode' (minify c) of
    Nothing ->
      let ex = mkIOError doesNotExistErrorType "loadAnnotations" Nothing (Just p)
      in ioError ex
    Just li -> return li

-- | A call
--
-- > loadDependencies summaryDir deps
--
-- Loads all of the 'LibraryInterface's transitively required by
-- @deps@ from any directory in @summaryDirs@.  The @summaryDirs@ are
-- searched in order.  Will throw an exception if a required
-- dependency is not found.
--
-- This variant will automatically include the C standard library (and
-- eventually the C++ standard library).
loadDependencies :: [FilePath] -> [String] -> IO DependencySummary
loadDependencies = loadDependencies' [CStdLib, LLVMLib]


-- | The same as 'loadDependencies', except it gives the option of not
-- automatically loading standard library summaries.
loadDependencies' :: [StdLib] -> [FilePath] -> [String] -> IO DependencySummary
loadDependencies' includeStd summaryDirs deps = do
  staticFiles <- getStaticFiles
  let baseDeps = foldl' (addStdlibDeps staticFiles) M.empty includeStd
  m <- loadTransDeps summaryDirs deps S.empty baseDeps
  let rcIx = indexRefCounts m
      rcObjs = indexStructuralSuperclasses m
  return $! DependencySummary m mempty rcIx rcObjs
  where
    errMsg n = error ("Foreign.Inference.Interface.loadDependencies': could not find interface " ++ n)
    lookupJson lib sfiles =
      fromMaybe (errMsg ("lib" ++ lib)) $ M.lookup (lib <.> "json") sfiles
    addStdlibDeps sfiles m CStdLib =
      let libc = lookupJson "c" sfiles
          libm = lookupJson "m" sfiles
          libdl = lookupJson "dl" sfiles
          libpthread = lookupJson "pthread" sfiles
          lc = decodeInterface libc
          lm = decodeInterface libm
          ldl = decodeInterface libdl
          lpthread = decodeInterface libpthread
          fs = concat [ libraryFunctions lc
                      , libraryFunctions lm
                      , libraryFunctions ldl
                      , libraryFunctions lpthread
                      ]
      in foldl' mergeFunction m fs
    addStdlibDeps sfiles m LLVMLib =
      let llvmIntrinsics = lookupJson "llvm" sfiles
          ll = decodeInterface llvmIntrinsics
      in foldl' mergeFunction m (libraryFunctions ll)


-- | Load all of the dependencies requested (transitively).  This just
-- iterates loading interfaces and recording all of the new
-- dependencies until there are no more.
--
-- Note that this function does not need to load types from library
-- descriptions because LLVM will have definitions for any public
-- struct types already.  The type descriptions are only useful for
-- binding generation.
loadTransDeps :: [FilePath] -> [String] -> Set String -> DepMap -> IO DepMap
loadTransDeps summaryDirs deps loadedDeps m = do
  let unmetDeps = filter (`S.notMember` loadedDeps) deps
      paths = map (<.> summaryExtension) unmetDeps
  case unmetDeps of
    [] -> return m
    _ -> do
      caps <- getNumCapabilities
      let acts = map (parseInterface summaryDirs) paths
      newInterfaces <- withPool caps $ \p -> parallel p acts
      let newDeps = concatMap libraryDependencies newInterfaces
          newFuncs = concatMap libraryFunctions newInterfaces
          loadedDeps' = loadedDeps `S.union` S.fromList unmetDeps
          m' = foldl' mergeFunction m newFuncs
      loadTransDeps summaryDirs newDeps loadedDeps' m'

-- | Try to "link" function summaries into the current
-- 'DependencySummary'.  This makes a best effort to deal with weak
-- symbols.  Weak symbols get overridden arbitrarily.  If two non-weak
-- symbols with the same name are encountered, this function just
-- raises an error.
mergeFunction :: DepMap -> ForeignFunction -> DepMap
mergeFunction m f = case M.lookup fn m of
  Nothing -> M.insert fn f m
  Just ForeignFunction { foreignFunctionLinkage = LinkWeak } -> M.insert fn f m
  Just f' -> case foreignFunctionLinkage f of
    LinkWeak -> m
    LinkDefault ->
      case f == f' of
        True -> m
        False ->
          $failure ("Functions with overlapping linkage: " ++ show f ++ " and " ++ show f')
  where
    fn = foreignFunctionName f

-- | This is a low-level helper to load a LibraryInterface from a
-- location on disk.
readLibraryInterface :: FilePath -> IO LibraryInterface
readLibraryInterface p = do
  c <- LBS.readFile p
  case decode' (minify c) of
    Nothing ->
      let ex = mkIOError doesNotExistErrorType "readLibraryInterface" Nothing (Just p)
      in ioError ex
    Just li -> return li

-- | This is a high-level interface that searches for a named library
-- in several locations (@summaryDirs@).
--
-- Try to load the named file from all possible summary repository
-- dirs.
parseInterface :: [FilePath] -> FilePath -> IO LibraryInterface
parseInterface summaryDirs p = do
  c <- loadFromSources summaryDirs p
  let mval = decode' (minify c)
  case mval of
    Nothing -> throw (DependencyDecodeError p)
    Just li -> return li

decodeInterface :: SBS.ByteString -> LibraryInterface
decodeInterface bs =
  let err = throw (DependencyDecodeError "builtin")
  in fromMaybe err $ decode' (minify (LBS.fromChunks [bs]))

loadFromSources :: [FilePath] -> FilePath -> IO LBS.ByteString
loadFromSources (src:rest) p = E.catch (LBS.readFile fname) handleMissingSrc
  where
    fname = src </> p
    handleMissingSrc :: IOException -> IO LBS.ByteString
    handleMissingSrc _ = loadFromSources rest p
loadFromSources [] p = throw (DependencyMissing p)

-- | Convert a Module to a LibraryInterface using the information in
-- the provided 'ModuleSummary's.
moduleToLibraryInterface :: Module   -- ^ Module to summarize
                            -> String   -- ^ Module name
                            -> [String] -- ^ Module dependencies
                            -> [ModuleSummary] -- ^ Summary information from analyses
                            -> ManualAnnotations
                            -> LibraryInterface
moduleToLibraryInterface m name deps summaries annots =
  LibraryInterface { libraryFunctions = funcs ++ aliases
                   , libraryTypes = map (id &&& annotateType) ts
                   , libraryName = name
                   , libraryDependencies = deps
                   , libraryEnums = moduleInterfaceEnumerations m
                   , libraryAnnotations = concatMap (summarizeModule m) summaries
                   }
  where
    ts = moduleInterfaceStructTypes m
    funcs = mapMaybe (functionToExternal summaries annots) (modDefines m)
    aliases = mapMaybe (functionAliasToExternal summaries annots) (modAliases m)
    annotateType t = concatMap (map fst . summarizeType t) summaries


functionAliasToExternal :: [ModuleSummary] -> ManualAnnotations -> GlobalAlias -> Maybe ForeignFunction
functionAliasToExternal summaries annots a =
  case valValue (valueContent' (aliasTarget a)) of
    ValSymbol (SymValDefine f) -> do
      -- Copy the visibility of the alias to the function.  It is often the case
      -- that an alias will be publically visible but the aliasee is not.  This way,
      -- we can fully re-use functionToExternal
      let f' = f { defVisibility = aliasVisibility a }
      e <- functionToExternal summaries annots f'
      return e { foreignFunctionName = (\(Symbol str) -> str) (aliasName a) }
    _ -> Nothing


-- | Summarize a single function.  Functions with types in their
-- signatures that have certain exotic types are not supported in
-- interfaces.
functionToExternal :: [ModuleSummary] -> ManualAnnotations -> Define -> Maybe ForeignFunction
functionToExternal summaries annots f =
  case vis of
    Just HiddenVisibility -> Nothing
    _ -> do
      lnk <- toLinkage (fromMaybe LLVM.External (defLinkage f))
      fretty <- typeToCType (functionReturnMetaUnsigned f) fretType
      let indexedArgs = zip [0..] (defArgs f)
      params <- mapM (paramToExternal summaries annots) indexedArgs
      return ForeignFunction { foreignFunctionName = (\(Symbol str) -> str) (defName f)
                             , foreignFunctionLinkage =
                                  if vis == Just ProtectedVisibility then LinkWeak else lnk
                             , foreignFunctionReturnType = fretty
                             , foreignFunctionParameters = params
                             , foreignFunctionAnnotations = fannots
                             }
  where
    vis = defVisibility f
    fannots = userFunctionAnnotations annots f ++
                concatMap (map fst . summarizeFunction f) summaries
    fretType = case getType f of
      FunTy rt _ _ -> rt
      t -> t

paramToExternal :: [ModuleSummary] -> ManualAnnotations -> (Int, Argument) -> Maybe Parameter
paramToExternal summaries annots (ix, arg) = do
  ptype <- typeToCType (paramMetaUnsigned arg) (argType arg)
  return Parameter { parameterType = ptype
                   , parameterName = argName arg
                   , parameterAnnotations =
                     userParameterAnnotations annots f ix ++
                              -- The map fst here drops witness information -
                              -- we don't need to expose that in summaries.
                       concatMap (map fst . summarizeArgument arg) summaries
                   }
  where
    f = argDefine arg

isVarArg :: Declare -> Bool
isVarArg ef = isVa
  where
    (FunTy _ _ isVa) = getType ef

userFunctionAnnotations :: ManualAnnotations -> Define -> [FuncAnnotation]
userFunctionAnnotations allAnnots f =
  case fannots of
    Nothing -> []
    Just (fas, _) -> fas
  where
    Symbol fname = defName f
    fannots = Map.lookup fname allAnnots

userParameterAnnotations :: ManualAnnotations -> Define -> Int -> [ParamAnnotation]
userParameterAnnotations allAnnots f ix =
  case fannots of
    Nothing -> []
    Just (_, pmap) -> IM.findWithDefault [] ix pmap

  where
    Symbol fname = defName f
    fannots = Map.lookup fname allAnnots

class (Monad m) => HasDependencies m where
  getDependencySummary :: m DependencySummary

lookupFunctionSummary :: (Show v, IsValue v,
                          SummarizeModule s, HasDependencies m,
                          MonadWriter Diagnostics m)
                         => s
                         -> v
                         -> m (Maybe [FuncAnnotation])
lookupFunctionSummary ms val = do
  ds <- getDependencySummary
  case valValue (valueContent' val) of
    ValSymbol (SymValDefine f) ->
      let fannots = userFunctionAnnotations (manualAnnotations ds) f
      in return $! Just $ fannots ++ map fst (summarizeFunction f ms)
    ValSymbol (SymValDeclare ef) -> do
      let Symbol fname = decName ef
          summ = depSummary ds
          extract = return . Just . foreignFunctionAnnotations
      maybe (missingDependency ef) extract (M.lookup fname summ)
    _ -> notAFunction val

-- | A variant of 'lookupFunctionSummary' where missing summaries can
-- be treated as simply returning no annotations.  Many analyses can
-- do this now that the missing summary warning is sunk down to this
-- level.
lookupFunctionSummaryList :: (Show v, IsValue v,
                              SummarizeModule s, HasDependencies m,
                              MonadWriter Diagnostics m)
                             => s
                             -> v
                             -> m [FuncAnnotation]
lookupFunctionSummaryList ms val =
  fromMaybe [] <$> lookupFunctionSummary ms val

lookupArgumentSummary :: (Show v, IsValue v,
                          SummarizeModule s, HasDependencies m,
                          MonadWriter Diagnostics m)
                         => s
                         -> v
                         -> Int
                         -> m (Maybe [ParamAnnotation])
lookupArgumentSummary ms val ix = do
  ds <- getDependencySummary
  case valValue (valueContent' val) of
    ValSymbol (SymValDefine f) ->
      case ix < length (defArgs f) of
        False -> return (Just [])
        True ->
          let annots = summarizeArgument (defArgs f !! ix) ms
              uannots = userParameterAnnotations (manualAnnotations ds) f ix
          in return $! Just $ uannots ++ map fst annots
    ValSymbol (SymValDeclare ef) -> do
      let Symbol fname = decName ef
          summ = depSummary ds
          -- Either this was a vararg or the function was cast to a
          -- strange type (with extra parameters) before being called.
          extract fsum =
            let ps = foreignFunctionParameters fsum
            in case ix < length ps of
              False -> return (Just [])
              True -> return $ Just $ parameterAnnotations (ps !! ix)
      maybe (missingDependency ef) extract (M.lookup fname summ)
    _ -> notAFunction val

-- | A variant of 'lookupArgumentSummary' where missing summaries can
-- be treated as simply returning no annotations.  Many analyses can
-- do this now that the missing summary warning is sunk down to this
-- level.
lookupArgumentSummaryList :: (Show v, IsValue v,
                              SummarizeModule s, HasDependencies m,
                              MonadWriter Diagnostics m)
                             => s
                             -> v
                             -> Int
                             -> m [ParamAnnotation]
lookupArgumentSummaryList ms val ix =
  fromMaybe [] <$> lookupArgumentSummary ms val ix

lookupStructFieldSummary :: (SummarizeModule s, HasDependencies m,
                             MonadWriter Diagnostics m)
                         => s
                         -> String
                         -> Integer
                         -> m (Maybe [StructFieldAnnotation])
lookupStructFieldSummary ms t s = do
  ds <- getDependencySummary
  let annots = summarizeStructField t s ms
      -- uannots = userStructFieldAnnotations (manualAnnotations ds) f ix
  return $! Just $ map fst annots

-- | A variant of 'lookupStructFieldSummary' where missing summaries can
-- be treated as simply returning no annotations.  Many analyses can
-- do this now that the missing summary warning is sunk down to this
-- level.
lookupStructFieldSummaryList :: (SummarizeModule s, HasDependencies m,
                              MonadWriter Diagnostics m)
                             => s
                             -> String
                             -> Integer
                             -> m [StructFieldAnnotation]
lookupStructFieldSummaryList ms t s =
  fromMaybe [] <$> lookupStructFieldSummary ms t s

notAFunction :: (Show v, MonadWriter Diagnostics m) => v -> m (Maybe a)
notAFunction _ = -- do
  -- let msg = "Not a function " ++ show val
  -- emitWarning Nothing "DependencyLookup" msg
  return Nothing

missingDependency :: (Show v, MonadWriter Diagnostics m) => v -> m (Maybe a)
missingDependency callee = do
  let msg = "Missing dependency summary for " ++ show callee
  emitWarning Nothing "DependencyLookup" msg
  return Nothing


-- Helpers

-- TODO: Need to consult some metadata here to get sign information
functionReturnMetaUnsigned :: Define -> Bool
functionReturnMetaUnsigned _ = False

-- | Convert an LLVM type to an external type.  Note that some types are
-- not supported in external interfaces (vectors and exotic floating
-- point types).
typeToCType :: Bool -> Type -> Maybe CType
typeToCType isUnsigned t = case t of
  Array _ t' -> do
    tt <- typeToCType isUnsigned t'
    return $! CPointer tt
  FunTy r ts _ -> do
    rt <- typeToCType False r
    tts <- mapM (typeToCType False) ts
    return $! CFunction rt tts
  PtrTo t' -> do
    tt <- typeToCType False t'
    return $! CPointer tt
  Struct (Right (Ident n)) _ _ -> return $! CStruct (sanitizeStructName n) []
  Struct (Left _) ts _ -> do
    tts <- mapM (typeToCType False) ts
    return $! CAnonStruct tts
  Vector _ _ -> Nothing
  Opaque _ -> Nothing
  PrimType p -> primtypeToCType isUnsigned p

primtypeToCType :: Bool -> PrimType -> Maybe CType
primtypeToCType isUnsigned t = case t of
  Void -> return CVoid
  Label -> Nothing
  Metadata -> Nothing
  Integer i ->
    case isUnsigned of
      False -> return $! CInt (fromIntegral i)
      True -> return $! CUInt (fromIntegral i)
  FloatType f -> floatTypeToCType f
  X86mmx -> Nothing

floatTypeToCType :: FloatType -> Maybe CType
floatTypeToCType t = case t of
  Float -> return CFloat
  Double -> return CDouble
  Fp128 -> Nothing
  X86_fp80 -> Nothing
  PPC_fp128 -> Nothing
  Half -> Nothing

-- | Convert an LLVM linkage to a type more suitable for the summary
-- If this function returns a Linkage, the function is exported in the
-- shared library interface.  Private (internal linkage) functions are
-- not exported and therefore not shown in the interface.
toLinkage :: LLVM.Linkage -> Maybe Linkage
toLinkage l = case l of
  LLVM.Private -> Nothing
  LLVM.LinkerPrivate -> Nothing
  LLVM.LinkerPrivateWeak -> Nothing
  LLVM.LinkerPrivateWeakDefAuto -> Nothing
  LLVM.Internal -> Nothing
  LLVM.AvailableExternally -> Just LinkDefault
  LLVM.Linkonce -> Just LinkWeak
  LLVM.Weak -> Just LinkWeak
  LLVM.Common -> Just LinkDefault
  LLVM.Appending -> Just LinkDefault
  LLVM.ExternWeak -> Just LinkWeak
  LLVM.LinkonceODR -> Just LinkWeak
  LLVM.WeakODR -> Just LinkWeak
  LLVM.External -> Just LinkDefault
  LLVM.DLLImport -> Just LinkDefault
  LLVM.DLLExport -> Just LinkDefault

{-# ANN module "HLint: ignore Use if" #-}
