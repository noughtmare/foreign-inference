{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes, PatternGuards #-}
{-# LANGUAGE ViewPatterns, DeriveGeneric, TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | This module defines a Nullable pointer analysis.  It actually
-- identifies non-nullable pointers (the rest are nullable).
--
-- A non-nullable pointer parameter @p@ such that, if @p@ is NULL, the
-- library will exhibit "undesirable" behavior.  Currently,
-- undesirable behavior is a segfault or a call to exit/abort.  In the
-- future, it will be extended to cover other types of error-reporting
-- behavior.
--
-- More precisely, a pseudo-algorithm for classifying pointers as
-- non-nullable is as follows.  Assume @p@ is NULL.  If *any* path
-- through the function reaches a return statement without executing
-- undesirable code, @p@ is nullable.
--
-- Checking all paths is expensive, so we approximate with dataflow
-- analysis:
--
--  * The dataflow fact at each program point is the set of arguments
--    that are NULL
--
--  * The meet operator is set union
--
--  * On conditional branches, arguments that are known to be not-null
--    on a branch (due to the branch condition) are removed from the
--    set
--
--  * If undesirable code is executed (dereference null, call exit,
--    etc), the argument that caused the error is removed from the
--    set.
--
--
-- This algorithm identifies those parameters whose NULL-ness *must*
-- cause an error.  This is an under-approximation of all of the
-- parameters we might like to be non-nullable, but it is a safe
-- approximation.  The algorithm will never prevent a parameter from
-- being NULL where that might permit some useful behavior (unless the
-- caller expects to catch a segfault somehow).
--
-- Infeasible paths are not a problem because, intuitively, the
-- algorithm does not reason about paths that might not be taken, only
-- the sum of the paths that MUST be taken.  Complex aliasing is also
-- not a problem, since we cannot prove that paths with complex
-- aliasing properties are taken we again do not bother reasoning
-- about them.
--
-- TODO: If a function can return without having *any* side effects
-- while a parameter is NULL, that parameter is not nullable.
--
-- > void bzero(char* p, int n) {
-- >   for(int i = 0; i < n; ++i ) {
-- >     p[i] = 0;
-- >   }
-- > }
--
-- In fact, passing NULL for p and 0 for n allows this function to be
-- called safely.  However, doing so has no value and it would be fair
-- to at least warn about seeing NULL passed for p here.
--
-- Possible implementation strategy: add a side-effect dataflow bit.
-- Merging the bits is an && operation.  If the bit is set at the end
-- of the function, there is a path with no side effects?  This
-- doesn't seem sufficient
module Foreign.Inference.Analysis.Nullable (
  -- * Interface
  NullableSummary,
  identifyNullable,
  -- * Testing
  nullSummaryToTestFormat
  ) where

import GHC.Generics ( Generic )

import Control.Arrow
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Getter, Lens', makeLenses, (.~), to, view )
import Control.Monad ( foldM )
import Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.Hashable (Hashable (..))

import LLVM.Analysis
import LLVM.Analysis.BlockReturnValue
import LLVM.Analysis.CDG
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow
import LLVM.Analysis.Dominance
import LLVM.Analysis.NullPointers

import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Analysis.ErrorHandling
import Foreign.Inference.Analysis.Return

-- import Text.Printf
import qualified Debug.Trace 

-- debug :: c -> String -> c
-- debug = flip trace

trace :: String -> a -> a
trace _ x = x
-- trace = Debug.Trace.trace

throughStruct :: Bool
throughStruct = True

data NullLoc
  = ArgLoc Argument
  | FieldLoc String        -- ^ struct identifier
             Integer       -- ^ field name
  deriving (Eq, Ord, Show, Generic, Hashable, NFData)

type SummaryType = HashMap NullLoc [Witness]

-- | Note, this could be a Set (Argument, Instruction) where the
-- Instruction is the fact we saw that led us to believe that Argument
-- is not nullable.
data NullableSummary =
  NullableSummary { _nullableSummary :: !SummaryType
                  , _nullableDiagnostics :: !Diagnostics
                  }
  deriving (Generic)

$(makeLenses ''NullableSummary)

instance Semigroup NullableSummary where
  (<>) = mappend

instance Monoid NullableSummary where
  mempty = NullableSummary mempty mempty
  mappend (NullableSummary s1 d1) (NullableSummary s2 d2) =
    NullableSummary (s1 `mappend` s2) (d1 `mappend` d2)

instance NFData NullableSummary where
  rnf = genericRnf

instance Eq NullableSummary where
  (NullableSummary s1 _) == (NullableSummary s2 _) = s1 == s2

instance SummarizeModule NullableSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeNullArgument
  summarizeStructField = summarizeNullStructField

summarizeNullArgument :: Argument -> NullableSummary -> [(ParamAnnotation, [Witness])]
summarizeNullArgument a (NullableSummary s _) =
  case HM.lookup (ArgLoc a) s of
    Nothing -> []
    Just ws -> [(PANotNull, ws)]

summarizeNullStructField :: String -> Integer -> NullableSummary -> [(StructFieldAnnotation, [Witness])]
summarizeNullStructField t f (NullableSummary s _) =
  case HM.lookup (FieldLoc t f) s of
    Nothing -> []
    Just ws -> [(SFNotNull, ws)]

identifyNullable :: forall funcLike compositeSummary .
                    (FuncLike funcLike, HasDefine funcLike,
                     HasCFG funcLike, HasNullSummary funcLike,
                     HasCDG funcLike, HasDomTree funcLike,
                     HasBlockReturns funcLike)
                    => DependencySummary
                    -> Lens' compositeSummary NullableSummary
                    -> Getter compositeSummary ReturnSummary
                    -> Getter compositeSummary (Maybe ErrorSummary)
                    -> ComposableAnalysis compositeSummary funcLike
identifyNullable ds lns retLens errLens =
  composableDependencyAnalysisM runner nullableAnalysis lns depLens
  where
    depLens :: Getter compositeSummary (ReturnSummary, Maybe ErrorSummary)
    depLens = to (view retLens &&& view errLens)
    runner a = runAnalysis a ds constData cache
    constData = ND mempty undefined undefined undefined undefined mempty
    cache = NState HM.empty

data NullData = ND { moduleSummary :: NullableSummary
                   , returnSummary :: ReturnSummary
                   , controlDepGraph :: CDG
                   , domTree :: DominatorTree
                   , nullPointersSummary :: NullPointersSummary
                   , blockRets :: BlockReturns
                   }

-- Change to a formula cache?
data NullState = NState { phiCache :: HashMap Stmt (Maybe Value) }

data NullLocs = NullLocsTop | NullLocsSet (Set NullLoc)
  deriving (Show, Eq, Ord)

instance Semigroup NullLocs where
  NullLocsTop <> _ = NullLocsTop 
  _ <> NullLocsTop = NullLocsTop 
  NullLocsSet x <> NullLocsSet y = NullLocsSet (x <> y)

instance Monoid NullLocs where
  mempty = NullLocsSet mempty
  mappend = (<>)

insertNullLoc :: NullLoc -> NullLocs -> NullLocs
insertNullLoc _ NullLocsTop = NullLocsTop
insertNullLoc x (NullLocsSet xs) = NullLocsSet (S.insert x xs)

nullLocsToList :: NullLocs -> [NullLoc]
nullLocsToList (NullLocsSet xs) = S.toList xs
nullLocsToList _ = error "Cannot convert Top to list (it would be infinite)"

meetNullLocs :: NullLocs -> NullLocs -> NullLocs
meetNullLocs NullLocsTop x = x
meetNullLocs x NullLocsTop = x
meetNullLocs (NullLocsSet x) (NullLocsSet y) =  NullLocsSet
  $  S.intersection x y
  <> S.filter isFieldLoc (x <> y)
  where
    isFieldLoc (FieldLoc _ _) = True
    isFieldLoc _ = False

  -- TODO remove this but remember it
  -- We want to do an intersection of the fieldlocs,
  -- but only in the control flow paths that are descendants of the struct access

data NullInfo = NInfo { nonNullLocations :: NullLocs
                      , nullWitnesses :: Map NullLoc (Set Witness)
                      }
              deriving (Eq, Ord, Show)

instance HasDiagnostics NullableSummary where
  diagnosticLens = nullableDiagnostics

type Analysis = AnalysisMonad NullData NullState

meetNullInfo :: NullInfo -> NullInfo -> NullInfo
meetNullInfo ni1 ni2 =
  NInfo { nonNullLocations = nonNullLocations ni1 `meetNullLocs` nonNullLocations ni2
        , nullWitnesses = M.unionWith S.union (nullWitnesses ni1) (nullWitnesses ni2)
        }

-- | The analysis that is applied to every function in the call graph.
-- It runs a dataflow analysis over the function to identify the
-- parameters that are used before they are known to be non-NULL.
--
-- This set of arguments is added to the global summary data (set of
-- all non-nullable arguments).
nullableAnalysis :: (FuncLike funcLike, HasCFG funcLike,
                     HasDefine funcLike, HasCDG funcLike,
                     HasNullSummary funcLike, HasDomTree funcLike,
                     HasBlockReturns funcLike)
                    => (ReturnSummary, Maybe ErrorSummary)
                    -> funcLike
                    -> NullableSummary
                    -> Analysis NullableSummary
nullableAnalysis (retSumm, errSumm) funcLike s@(NullableSummary summ _) = do
  -- Run this sub-analysis step with a modified environment - the
  -- summary component is the current module summary (given to us by
  -- the SCC traversal).
  --
  -- The initial state of the dataflow analysis is top -- all pointer
  -- parameters are NULLable.
  let envMod e = e { moduleSummary = s
                   , returnSummary = retSumm
                   , controlDepGraph = getCDG funcLike
                   , domTree = getDomTree funcLike
                   , nullPointersSummary = nps
                   , blockRets = getBlockReturns funcLike
                   }
      args = filter isPointer (defArgs f)
      top = NInfo NullLocsTop mempty
      fact0 = NInfo mempty mempty
      analysis = fwdDataflowAnalysis top meetNullInfo (nullTransfer errSumm)
  localInfo <- analysisLocal envMod (dataflow funcLike analysis fact0)

  let exitInfo = dataflowResult localInfo
      notNullableLocs = nonNullLocations exitInfo
      annotateWithWitness = attachWitness (nullWitnesses exitInfo)
      locsAndWitnesses = map annotateWithWitness (nullLocsToList notNullableLocs)

  -- Update the module symmary with the set of pointer parameters that
  -- we have proven are accessed unchecked.
  let newSumm = foldr (\(a, ws) acc -> HM.insert a ws acc) summ locsAndWitnesses
  return $! (nullableSummary .~ newSumm) s
  where
    f = getDefine funcLike
    nps = getNullSummary funcLike

attachWitness :: Map NullLoc (Set Witness)
                 -> NullLoc
                 -> (NullLoc, [Witness])
attachWitness m a =
  case M.lookup a m of
    Nothing -> (a, [])
    Just is -> (a, S.toList is)

{-
nullEdgeTransfer :: NullInfo -> Instruction -> Analysis [(BasicBlock, NullInfo)]
nullEdgeTransfer ni i = return $ fromMaybe [] $ do
  (_, val, notNullBlock) <- branchNullInfo i
  arg <- fromValue val
  return [(notNullBlock, ni { nonNullLocations = S.insert arg (nonNullLocations ni) })]
-}

nullTransfer :: Maybe ErrorSummary -> NullInfo -> Stmt -> Analysis NullInfo
nullTransfer Nothing ni i = nullTransfer' ni i
nullTransfer (Just errSumm) ni i
  | stmtIsTerminator i = do
    brs <- analysisEnvironment blockRets
    let bb = stmtBasicBlock i
        f = bbDefine bb
    case blockReturn brs bb of
      Nothing -> nullTransfer' ni i
      Just rv -> do
        let 
          descs
            | prettySymbol (defName f) == "@MHD_set_connection_value" = [ErrorDescriptor mempty (ReturnConstantInt (S.singleton 0)) []]
            | otherwise = errorDescriptors errSumm f
        case any (matchesReturnValue rv) descs of
          False -> trace ("NO ERROR RET: " ++ prettySymbol (defName f) ++ ", stmt: " ++ show (stmtInstr i) ++ ", value: " ++ show (valValue rv) ++ ", descs: " ++ show descs) $ nullTransfer' ni i
          True -> trace ("ERROR RET: " ++ prettySymbol (defName f) ++ ", stmt: " ++ show (stmtInstr i) ++ ", value " ++ show (valValue rv)) $ do
            let formals = S.fromList $ map ArgLoc $ defArgs f
                ni' = ni { nonNullLocations = NullLocsSet formals
                         , nullWitnesses =
                           S.foldl' (addWitness "arg/ret-error" i) (nullWitnesses ni) formals
                         }
            trace ("arg/ret-error: " ++ show formals) $ nullTransfer' ni' i
  | otherwise = nullTransfer' ni i

matchesReturnValue :: Value -> ErrorDescriptor -> Bool
matchesReturnValue (valValue -> ValInteger v) d =
  case errorReturns d of
    ReturnConstantPtr _ -> False -- we don't really use these
    ReturnConstantInt is -> S.member (fromIntegral v) is
matchesReturnValue _ _ = False


-- | First, process the incoming CFG edges to learn about pointers
-- that are known to be non-NULL.  Then use this updated information
-- to identify pointers that are dereferenced when they *might* be
-- NULL.  Also map these possibly-NULL pointers to any corresponding
-- parameters.
nullTransfer' :: NullInfo -> Stmt -> Analysis NullInfo
nullTransfer' ni i =
  case stmtInstr i of
    Load ptr _ _ ->
      valueDereferenced i ptr ni
    Store x ptr _ _ -> trace "STORE" $ 
      valueStored i x ptr =<< valueDereferenced i ptr ni
    AtomicRW _ _ ptr _ _ _ ->
      valueDereferenced i ptr ni
    CmpXchg _ _ ptr _ _ _ _ _ ->
      valueDereferenced i ptr ni

    Call _ _ calledFunc args ->
      callTransfer i (stripBitcasts calledFunc) args ni
    Invoke _ calledFunc args _ _ ->
      callTransfer i (stripBitcasts calledFunc) args ni

    _ -> return ni

-- valueStructName :: Value -> Maybe String
-- valueStructName (Value { valType = PtrTo (Struct (Right name) _ _) }) = Just name
-- valueStructName _ = Nothing

valueStored :: Stmt -> Value -> Value -> NullInfo -> Analysis NullInfo
valueStored i x v ni | throughStruct = do
  modSumm <- analysisEnvironment moduleSummary
  v' <- mustExecuteValue (stripBitcasts v)
  trace ("must execute store: " ++ show v') $ case v' of
    Just v'' -> 
      case valValue v'' of
        ValIdent (IdentValStmt (stmtInstr -> GEP _
            (Value { valType = PtrTo (Struct (Right name) _ _) })
            [_, valValue -> ValInteger f])) -> do
          let 
            t = prettyIdent name
          sfSum <- trace ("lookup sf: " ++ show (t, f)) $ lookupStructFieldSummaryList modSumm t f
          if SFNotNull `elem` sfSum
             then trace ("IS NOT NULL!") $ valueDereferenced i x ni
             else pure ni
        ValIdent (IdentValStmt (stmtInstr -> x)) -> trace ("Other instruction: " ++ show x) (pure ni)
        ValIdent x -> trace ("Other ident: " ++ show x) (pure ni)
        _ -> pure ni
    _ -> pure ni
valueStored _ _ _ ni = pure ni

valueDereferenced :: Stmt -> Value -> NullInfo -> Analysis NullInfo
valueDereferenced i ptr ni
  | Just v <- memAccessBase ptr = do
      v' <- mustExecuteValue v
      trace ("must execute deref: " ++ show v') $ return $ fromMaybe ni $ do
        v'' <- v'
        case valValue v'' of
          ValIdent (IdentValStmt (stmtInstr -> GEP _
            (Value { valType = PtrTo (Struct (Right name) _ _) })
            [_, valValue -> ValInteger i])) | throughStruct ->
              trace ("struct field deref: " ++ prettyIdent name ++ "." ++ show i) $ return ni
                { nonNullLocations = insertNullLoc (FieldLoc (prettyIdent name) i) (nonNullLocations ni)
                }
          ValIdent (IdentValArgument arg) -> do
            let w = Witness i "deref"
            trace ("arg deref: " ++ show arg) $ return ni
              { nonNullLocations = insertNullLoc (ArgLoc arg) (nonNullLocations ni)
              , nullWitnesses = MS.insertWith S.union (ArgLoc arg) (S.singleton w) ws
              }
          _ -> Nothing
  | otherwise = return ni
  where
    ws = nullWitnesses ni


-- TODO generalize and move this
showStmtInstr = show . fmap stmtInstr . valueStmt . valValue

valueStmt (ValIdent (IdentValStmt s)) = Just s
valueStmt _ = Nothing


-- | Given a value that is being dereferenced by an instruction
-- (either a load, store, or atomic memory op), determine the *base*
-- address that is being dereferenced.
--
-- Not all base values need to be analyzed.  For example, globals and
-- allocas are *always* safe to dereference.
--
-- This function strips off intermediate bitcasts.
memAccessBase :: Value -> Maybe Value
memAccessBase ptr =
  case valValue (valueContent' ptr) of
    ValSymbol (SymValGlobal _) -> Nothing
    ValIdent (IdentValStmt (stmtInstr -> Alloca {})) -> Nothing
    -- For optimized code, arguments (which we care about) can be
    -- loaded/stored to directly (without an intervening alloca).
    ValIdent (IdentValArgument a) -> Just (toValue a)
    -- In this case, we have two levels of dereference.  The first
    -- level (la) is a global or alloca (or result of another
    -- load/GEP).  This represents a source-level dereference of a
    -- local pointer.
    ValIdent (IdentValStmt (stmtInstr -> Load la _ _)) ->
      Just (stripBitcasts la)
    -- GEP instructions can appear in sequence for nested field
    -- accesses.  We want the base of the access chain, so walk back
    -- as far as possible and return the lowest-level GEP base.
    ValIdent (IdentValStmt (stmtInstr -> GEP _ base _)) ->
      memAccessBase base
    _ -> Just (stripBitcasts ptr)

-- | A split out transfer function for function calls.  Looks up
-- summary values for called functions/params and records relevant
-- information in the current dataflow fact.
callTransfer ::  Stmt
                 -> Value
                 -> [Value]
                 -> NullInfo
                 -> Analysis NullInfo
callTransfer i calledFunc args ni = do
  let indexedArgs = zip [0..] args
  modSumm <- analysisEnvironment moduleSummary
  retSumm <- analysisEnvironment returnSummary
--  nullSumm <- analysisEnvironment nullPointersSummary
  retAttrs <- lookupFunctionSummaryList retSumm calledFunc

  let bb = stmtBasicBlock i
      f = bbDefine bb
      formals = S.fromList $ map ArgLoc $ filter isPointer $ defArgs f
  -- let nullValues = nullPointersAt nullSumm i
  --     nullArgs :: Set Argument
  --     nullArgs = S.fromList $ mapMaybe fromValue nullValues
  ni' <- case FANoRet `elem` retAttrs of
    True -> trace ("arg/noret callTransfer: " ++ show (f, formals))
      $ return ni { nonNullLocations = NullLocsSet formals
                  , nullWitnesses =
                    S.foldl' (addWitness "arg/noret" i) (nullWitnesses ni) formals
                  }

    False -> foldM (checkArg modSumm) ni indexedArgs

  -- We also learn information about pointers that are not null if
  -- this is a call through a function pointer (calling a NULL
  -- function pointer is illegal)
  case isIndirectCallee calledFunc of
    False -> return ni'
    True -> valueDereferenced i calledFunc ni'
  where
    checkArg ms acc (ix, arg) = do
      attrs <- lookupArgumentSummaryList ms calledFunc ix
      case PANotNull `elem` attrs of
        False -> return acc
        True -> valueDereferenced i arg acc

addWitness :: String
              -> Stmt
              -> Map NullLoc (Set Witness)
              -> NullLoc
              -> Map NullLoc (Set Witness)
addWitness reason i m a =
  MS.insertWith S.union a (S.singleton (Witness i reason)) m

isIndirectCallee :: Value -> Bool
isIndirectCallee val =
  case valValue (valueContent' val) of
    ValSymbol (SymValDefine _) -> False
    ValSymbol (SymValDeclare _) -> False
    _ -> True

-- We can tell that a piece of code MUST execute if:
--
-- 1) It has no control dependencies, or
--
-- 2) It has exactly one control dependency (a direct one, and no
-- indirect cdeps) AND all incoming non-backedges are unconditional
-- branches.

-- | Given a Value, figure out which of its sub-values *MUST* be
-- executed on *SOME* call to the function.  For most Values, this is
-- the identity.
--
-- For Select instructions, the result is Nothing (unless we decide to
-- reason more thoroughly about the select condition).
--
-- For Phi nodes, there may be a result for do-while style loops where
-- the first iteration must always be taken.  In this case, return the
-- value that *MUST* be accessed on that iteration.


mustExecuteValue :: Value -> Analysis (Maybe Value)
mustExecuteValue v =
  case valValue (valueContent' v) of
    ValIdent (IdentValStmt (stmtInstr -> Select {})) -> return Nothing
    ValIdent (IdentValStmt i@(stmtInstr -> Phi _ ivs)) -> do
      s <- analysisGet
      case HM.lookup i (phiCache s) of
        Just mv -> return mv
        Nothing -> do
          mv <- mustExec' i ivs
          analysisPut s { phiCache = HM.insert i mv (phiCache s) }
          return mv
    _ -> return (Just v)

mustExec' :: Stmt -> [(Value, BasicBlock)] -> Analysis (Maybe Value)
mustExec' i ivs = do
  cdg <- analysisEnvironment controlDepGraph
  dt <- analysisEnvironment domTree
  let cdeps = directControlDependencies cdg i
  case cdeps of
    [] -> return Nothing
    [_] -> do
      let predTerms = map (second (last . bbStmts)) ivs
          nonBackedges = filter (isNotBackedge dt i) predTerms
      case filter (isUnconditional . stmtInstr . snd) nonBackedges of
        [] -> return Nothing
        [(v,_)] -> return (Just v)
        _ -> return Nothing
    _ -> return Nothing
  where
    isUnconditional Jump {} = True
    isUnconditional _ = False
    isNotBackedge g inst (_, br) = not (dominates g inst br)

isPointer :: (IsValue v) => v -> Bool
isPointer v = case valType (toValue v) of
  (PtrTo _) -> True
  _ -> False


-- Testing

-- | Convert the 'NullableSummary' to a format that is easy to read
-- from a file for testing purposes.
nullSummaryToTestFormat :: NullableSummary -> Map String (Set String)
nullSummaryToTestFormat (NullableSummary m _) =
  foldr addArg M.empty (HM.toList m)
  where
    addArg (ArgLoc a, _) acc =
      let f = argDefine a
          k = prettySymbol (defName f)
          v = S.singleton (argName a)
      in MS.insertWith S.union k v acc
    addArg (FieldLoc struct field, _) acc =
      let k = struct
          v = S.singleton (show field)
      in MS.insertWith S.union k v acc
