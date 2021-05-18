{-# LANGUAGE TemplateHaskell #-}
module Foreign.Inference.Interface.Metadata (
  moduleInterfaceEnumerations,
  moduleInterfaceStructTypes,
  paramMetaUnsigned,
  defReturnMetaUnsigned,
  -- * Helper
  sanitizeStructName
  ) where

import Control.Arrow ( (&&&) )
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as M
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import qualified Data.Set as S
import Data.Maybe ( catMaybes, fromMaybe, mapMaybe, fromJust )
import Data.Monoid
import Data.Text ( Text )
import qualified Data.Text as T
import Debug.Trace.LocationTH
import qualified Data.Map as Map

import LLVM.Analysis

import Data.Graph.Interface
import Data.Graph.MutableDigraph
import Data.Graph.Algorithms.DFS

import Foreign.Inference.Interface.Types

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- | Collect all of the enumerations used in the external interface of
-- a Module by inspecting metadata.
moduleInterfaceEnumerations :: Module -> [CEnum]
moduleInterfaceEnumerations =
  S.toList . S.fromList . foldr (collectEnums . umValues) [] . modUnnamedMd

moduleInterfaceStructTypes :: Module -> [CType]
moduleInterfaceStructTypes m = opaqueTypes ++ concreteTypes
  where
    defFuncs = modDefines m
    (interfaceTypeMap, noMDTypes) = foldr extractInterfaceStructTypes (mempty, mempty) defFuncs
    unifiedTypes = M.keys interfaceTypeMap
    unifiedMDTypes = map (findTypeMD interfaceTypeMap) unifiedTypes
    sortedUnifiedMDTypes = typeSort unifiedMDTypes
    concreteTypes = map metadataStructTypeToCType sortedUnifiedMDTypes
    concreteNameSet = S.fromList $ mapMaybe ctypeStructName concreteTypes

    opaqueLLVMTypes = HS.toList noMDTypes
    uniqueOpaqueTypeNames = HS.toList $ HS.fromList $ map structTypeName opaqueLLVMTypes
    opaqueTypes0 = map toOpaqueCType uniqueOpaqueTypeNames
    opaqueTypes = filter nameNotConcrete opaqueTypes0

    nameNotConcrete (CStruct n _) = not (S.member n concreteNameSet)
    nameNotConcrete t = $failure ("Expected struct type: " ++ show t)

-- | Collect all of the struct types (along with their metadata) used
-- in the external interface of a Module.
-- moduleInterfaceStructTypes :: Module -> HashMap Type ValMd
-- moduleInterfaceStructTypes =
--   foldr extractInterfaceStructTypes M.empty . modDefines

structTypeName :: Type -> String
structTypeName (Struct (Right (Ident name)) _ _) = sanitizeStructName name
structTypeName (Struct (Left tid) _ _) = "anon" ++ show tid
structTypeName t = $failure ("Expected struct type: " ++ show t)

toOpaqueCType :: String -> CType
toOpaqueCType name = CStruct name []

ctypeStructName :: CType -> Maybe String
ctypeStructName (CStruct n _) = Just n
ctypeStructName _ = Nothing

-- | Match up a type with its metadata
findTypeMD :: HashMap Type ValMd -> Type -> (Type, ValMd)
findTypeMD interfaceTypeMap t =
  case M.lookup t interfaceTypeMap of
    Nothing -> $failure ("No metadata found for type: " ++ show t)
    Just md -> (t, md)


extractInterfaceEnumTypes :: Define -> [CEnum] -> [CEnum]
extractInterfaceEnumTypes f acc =
  foldr collectEnums acc typeMds
  where
    retMd = defReturnTypeValMd f
    argMds = map paramTypeValMd (defArgs f)
    typeMds = catMaybes $ retMd : argMds

collectEnums :: ValMd -> [CEnum] -> [CEnum]
collectEnums = go Nothing
  where
    go _ (ValMdDebugInfo (DebugInfoDerivedType DIDerivedType { didtName = bsname
                                             , didtTag = DW_TAG_typedef
                                             , didtBaseType = Just parent
                                             })) acc =
      go (Just (fromMaybe "" bsname)) parent acc
    go name (ValMdDebugInfo (DebugInfoDerivedType DIDerivedType { didtBaseType = Just parent })) acc =
      go name parent acc
    go name (ValMdDebugInfo (DebugInfoCompositeType DICompositeType
      { dictTag = DW_TAG_enumeration_type
      , dictName = bsname
      , dictElements = Just (ValMdNode enums)
      })) acc =
      case bsname of
        Nothing ->
          CEnum { enumName = fromMaybe "" name
                , enumValues = mapMaybe toEnumeratorValue enums
                } : acc
        Just bsname' ->
          CEnum { enumName = bsname'
                , enumValues = mapMaybe toEnumeratorValue enums
                } : acc
    go _ _ acc = acc

toEnumeratorValue :: Maybe ValMd -> Maybe (String, Int)
toEnumeratorValue (Just (ValMdDebugInfo (DebugInfoEnumerator ename eval))) =
  Just (ename, fromIntegral eval)
toEnumeratorValue _ = Nothing

extractInterfaceStructTypes :: Define
                               -> (HashMap Type ValMd, HashSet Type)
                               -> (HashMap Type ValMd, HashSet Type)
extractInterfaceStructTypes f (typeMDMap, opaqueTypes) =
  (typesWithMD, otherStructs `HS.union` opaqueTypes)
  where
    (structsWithMD, otherStructs) = foldr toStructType (mempty, mempty) typeMds
    typesWithMD = foldr addTypeMdMapping typeMDMap structsWithMD

    rt = defRetType f
    retMd = defReturnTypeValMd f
    argMds = map (argType &&& paramTypeValMd) (defArgs f)
    typeMds = (rt, retMd) : argMds
    addTypeMdMapping (llvmType, md) = M.insert llvmType md

toStructType :: (Type, Maybe ValMd)
                -> ([(Type, ValMd)], HashSet Type)
                -> ([(Type, ValMd)], HashSet Type)
toStructType (t@(Struct (Right _) _ _),
              Just (ValMdDebugInfo (DebugInfoDerivedType DIDerivedType
                { didtTag = DW_TAG_typedef
                , didtBaseType = parent
                }))) acc =
  toStructType (t, parent) acc
toStructType (t@(Struct (Right _) _ _), Just a) (tms, ts) = ((t, a) : tms, ts)
toStructType (PtrTo inner,
              Just (ValMdDebugInfo (DebugInfoDerivedType DIDerivedType
                { didtTag = DW_TAG_pointer_type
                , didtBaseType = parent
                }))) acc =
  toStructType (inner, parent) acc
toStructType (t@(PtrTo _),
              Just (ValMdDebugInfo (DebugInfoDerivedType DIDerivedType
                { didtBaseType = parent}))) acc =
  toStructType (t, parent) acc
toStructType (PtrTo inner, Nothing) acc =
  toStructType (inner, Nothing) acc
toStructType (t@Struct {}, Nothing) (tms, ts) =
  (tms, HS.insert t ts)
toStructType _ acc = acc

sanitizeStructName :: String -> String
sanitizeStructName = structBaseName

metadataStructTypeToCType :: (Type, ValMd) -> CType
metadataStructTypeToCType (Struct (Right (Ident name)) members _,
                           ValMdDebugInfo (DebugInfoCompositeType DICompositeType { dictElements =
                                                    Just (ValMdNode cmembers)
                                               })) =
  let memberTypes = zip members cmembers
      mtys = mapM trNameAndType memberTypes
  in CStruct (sanitizeStructName name) $ fromMaybe [] mtys
  where
    trNameAndType (llvmType, Just (ValMdDebugInfo (DebugInfoDerivedType DIDerivedType
      { didtName = Just memberName
      }))) = do
      realType <- structMemberToCType llvmType
      return (memberName, realType)
    trNameAndType _ = Nothing
-- If there were no members in the metadata, this is an opaque type
metadataStructTypeToCType (Struct (Right (Ident name)) _ _, _) =
  CStruct (sanitizeStructName name) []
metadataStructTypeToCType t =
  $failure ("Unexpected non-struct metadata" {- ++ show t -})

structMemberToCType :: Type -> Maybe CType
structMemberToCType t = case t of
  PrimType (Integer i) -> return $! CInt (fromIntegral i)
  PrimType (FloatType Float) -> return CFloat
  PrimType (FloatType Double) -> return CDouble
  Array n t' -> do
    tt <- structMemberToCType t'
    return $! CArray tt (fromIntegral n) -- FIXME lossy fromIntegral
  FunTy r ts _ -> do
    rt <- structMemberToCType r
    tts <- mapM structMemberToCType ts
    return $! CFunction rt tts
  PtrTo t' -> do
    tt <- structMemberToCType t'
    return $! CPointer tt
  Struct (Right (Ident n)) _ _ ->
    let name' = sanitizeStructName n
    in return $! CStruct name' []
  Struct (Left _) ts _ -> do
    tts <- mapM structMemberToCType ts
    return $! CAnonStruct tts
  PrimType Void -> return CVoid
  PrimType (FloatType Fp128) -> return $! CArray (CInt 8) 16
  -- Fake an 80 bit floating point number with an array of 10 bytes
  PrimType (FloatType X86_fp80) -> return $! CArray (CInt 8) 10
  PrimType (FloatType PPC_fp128) -> return $! CArray (CInt 8) 16
  PrimType X86mmx -> Nothing
  PrimType Label -> Nothing
  PrimType Metadata -> Nothing
  Vector _ _ -> Nothing
  Opaque _ -> Nothing
  PrimType (FloatType Half) -> Nothing

paramMetaUnsigned :: Argument -> Bool
paramMetaUnsigned a =
  fromMaybe False $ argMd a >>= \md -> do
    ValMdDebugInfo (DebugInfoLocalVariable DILocalVariable { dilvType = Just lt }) <- return md
    case lt of
      ValMdDebugInfo (DebugInfoBasicType DIBasicType { dibtEncoding = DW_ATE_unsigned }) -> return True
      ValMdDebugInfo (DebugInfoDerivedType DIDerivedType { didtBaseType = Just baseType }) ->
        case baseType of
          ValMdDebugInfo (DebugInfoBasicType DIBasicType { dibtEncoding = DW_ATE_unsigned }) -> return True
          _ -> fail "Not unsigned"
      _ -> fail "Not unsigned"

takeFirst :: [b] -> (b -> Maybe a) -> Maybe a
takeFirst [] _ = Nothing
takeFirst (x:xs) f =
  case f x of
    Nothing -> takeFirst xs f
    j -> j

paramTypeValMd :: Argument -> Maybe ValMd
paramTypeValMd a =
  argMd a >>= \md -> do
    ValMdDebugInfo (DebugInfoLocalVariable DILocalVariable { dilvType = lt }) <- return md
    lt

defReturnMetaUnsigned :: Define -> Bool
defReturnMetaUnsigned f =
  fromMaybe False $ takeFirst (Map.elems (defMetadata f)) $ \md -> do
    ValMdDebugInfo (DebugInfoSubprogram DISubprogram { dispType = ftype }) <- return md
    ValMdDebugInfo (DebugInfoCompositeType DICompositeType { dictElements = ms }) <- ftype
    ValMdNode (Just (ValMdDebugInfo rt) : _) <- ms
    case rt of
      DebugInfoDerivedType DIDerivedType { didtBaseType =
        Just (ValMdDebugInfo (DebugInfoBasicType DIBasicType { dibtEncoding = DW_ATE_unsigned }))} -> return True
      DebugInfoBasicType DIBasicType { dibtEncoding = DW_ATE_unsigned } -> return True
      _ -> fail "Not unsigned"

defReturnTypeValMd :: Define -> Maybe ValMd
defReturnTypeValMd f = takeFirst (Map.elems (defMetadata f)) $ \md -> do
  ValMdDebugInfo (DebugInfoSubprogram DISubprogram { dispType =
    Just (ValMdDebugInfo (DebugInfoCompositeType DICompositeType { dictElements =
      Just (ValMdNode (rt : _)) })) }) <- return md
  rt

type TypeGraph = SparseDigraph (Type, ValMd) ()

-- | All of the components of a type that are stored by-value must be
-- defined before that type can be defined.  This is a topological
-- ordering captured by this graph-based sort.
typeSort :: [(Type, ValMd)] -> [(Type, ValMd)]
typeSort ts = reverse $ topsort' g
  where
    g :: TypeGraph
    g = mkGraph ns es

    toNodeMap = M.fromList (zip (map fst ts) [0..])
    ns = zip [0..] ts
    es = concatMap toEdges ts

    toEdges :: (Type, ValMd) -> [Edge TypeGraph]
    toEdges (t@(Struct _ members _), _) =
      case M.lookup t toNodeMap of
        Nothing -> $failure ("Expected node id for type: " ++ show t)
        Just srcid -> mapMaybe (toEdge srcid) members
    toEdges _ = []

    toEdge :: Vertex -> Type -> Maybe (Edge TypeGraph)
    toEdge srcid t = do
      dstid <- M.lookup t toNodeMap
      return $! Edge srcid dstid ()

{-# ANN module "HLint: ignore Use if" #-}
