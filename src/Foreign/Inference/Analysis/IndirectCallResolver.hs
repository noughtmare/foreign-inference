{-# LANGUAGE ViewPatterns #-}
-- | FIXME: Currently there is an exception allowing us to identify
-- finalizers that are called through function pointers if the
-- function pointer is global and has an initializer.
--
-- This needs to be generalized to cover things that are initialized
-- once in the library code with a finalizer.  This will be a lower-level
-- analysis that answers the query:
--
-- > initializedOnce :: Value -> Maybe Value
--
-- where the returned value is the single initializer that was sourced
-- within the library.  This can be the current simple analysis for
-- globals with initializers.  Others will be analyzed in terms of
-- access paths (e.g., Field X of Type Y is initialized once with
-- value Z).
--
-- Linear scan for all stores, recording their access path.  Also look
-- at all globals (globals can be treated separately).  If an access
-- path gets more than one entry, stop tracking it.  Only record
-- stores where the value is some global entity.
--
-- Run this analysis after or before constructing the call graph and
-- initialize the whole-program summary with it.  It doesn't need to
-- be computed bottom up as part of the call graph traversal.
module Foreign.Inference.Analysis.IndirectCallResolver (
  IndirectCallSummary,
  identifyIndirectCallTargets,
  indirectCallInitializers,
  indirectCallTargets
  ) where

import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Maybe ( fromMaybe )
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.ClassHierarchy
import LLVM.Analysis.PointsTo
import LLVM.Analysis.PointsTo.Andersen

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- | This isn't a true points-to analysis because it is an
-- under-approximation.  However, that is sufficient for this library.
instance PointsToAnalysis IndirectCallSummary where
  mayAlias _ _ _ = True
  pointsTo = indirectCallInitializers
  resolveIndirectCall = indirectCallTargets

data IndirectCallSummary =
  ICS { summaryTargets :: Andersen
      , resolverCHA :: CHA
      , globalInits :: HashMap (Type, Int) (HashSet Value)
      }

constExpr' :: ConstExpr -> ConstExpr
constExpr' (ConstConv BitCast (valValue -> ValConstExpr x) _) = constExpr' x
constExpr' (ConstConv BitCast _ _) = error "Unexpected constant bitcast of non-ConstantExpr"
constExpr' x = x

-- If i is a Load of a global with an initializer (or a GEP of a
-- global with a complex initializer), just use the initializer to
-- determine the points-to set.  Obviously this isn't general.
--
-- Eventually, this should call down to a real (field-based) points-to
-- analysis for other values.
indirectCallInitializers :: IndirectCallSummary -> Value -> [Value]
indirectCallInitializers ics v =
  case valValue (valueContent' v) of
    ValSymbol (SymValDefine f) -> [toValue f]
    ValSymbol (SymValDeclare ef) -> [toValue ef]
    ValIdent (IdentValStmt li@(stmtInstr -> Load (valueContent' ->
      ValInstr (GEP _ base
        [ valValue -> ValInteger 0, valValue -> ValInteger (fromIntegral -> ix)]
        )) _ _)) -> fromMaybe (lookupStmt li) $ do
      let baseTy = valType base
      globInits <- HM.lookup (baseTy, ix) (globalInits ics)
      return $ HS.toList globInits ++ lookupStmt li
    -- Here, walk the initializer if it isn't a simple integer
    -- constant We discard the first index because while the global
    -- variable is a pointer type, the initializer is not (because all
    -- globals get an extra indirection as r-values)
    ValIdent (IdentValStmt li@(stmtInstr -> Load (valValue . valueContent' ->
      ValConstExpr (constExpr' ->
        ConstGEP _ _ _ ((valValue . valueContent' -> ValSymbol (SymValGlobal Global { globalValue = Just i }))
          : (valValue -> ValInteger 0)
          : ixs))) _ _)) ->
      maybe (lookupStmt li) (:[]) $ resolveInitializer i ixs
    ValIdent (IdentValStmt li@(stmtInstr -> Load (valValue . valueContent' ->
      ValSymbol (SymValGlobal Global { globalValue = Just i })) _ _)) ->
      case valValue (valueContent' i) of
        -- All globals have some kind of initializer; if it is a zero
        -- or constant (non-function) initializer, just ignore it and
        -- use the more complex fallback.
        -- FIXME
        ValSymbol _ -> [i]
        ValIdent _ -> [i]
        _ -> lookupStmt li
    ValIdent (IdentValStmt li@(stmtInstr -> Load {})) ->
      lookupStmt li
    ValIdent (IdentValStmt i) -> lookupStmt i
    _ -> []
  where
    lookupStmt i = pointsTo (summaryTargets ics) (toValue i)

resolveInitializer :: Value -> [Value] -> Maybe Value
resolveInitializer v [] = return (stripBitcasts v)
resolveInitializer v (ix:ixs) = do
  intVal <- fromConstantInt ix
  case valValue v of
    ValArray _ vs ->
      if length vs <= intVal then Nothing else resolveInitializer (vs !! intVal) ixs
    ValStruct vs _ ->
      if length vs <= intVal then Nothing else resolveInitializer (vs !! intVal) ixs
    _ -> Nothing

fromConstantInt :: Value -> Maybe Int
fromConstantInt (valValue -> ValInteger iv) = Just $ fromIntegral iv
fromConstantInt _ = Nothing

-- | Resolve the targets of an indirect call instruction.  This works
-- with both C++ virtual function dispatch and some other common
-- function pointer call patterns.  It is unsound and incomplete.
indirectCallTargets :: IndirectCallSummary -> Instr -> [Value]
indirectCallTargets ics i =
  -- If this is a virtual function call (C++), use the virtual
  -- function resolver.  Otherwise, fall back to the normal function
  -- pointer analysis.
  maybe fptrTargets (fmap toValue) vfuncTargets
  where
    vfuncTargets = resolveVirtualCallee (resolverCHA ics) i
    fptrTargets =
      case i of
        Call _ _  f _    -> indirectCallInitializers ics f
        Invoke _ f _ _ _ -> indirectCallInitializers ics f
        _ -> []

-- | Run the initializer analysis: a cheap pass to identify a subset
-- of possible function pointers that object fields can point to.
identifyIndirectCallTargets :: Module -> IndirectCallSummary
identifyIndirectCallTargets m =
  ICS (runPointsToAnalysisWith ignoreNonFptr m) (runCHA m) (gis)
  where
    ignoreNonFptr = ignoreNonFptrType . valType
    ignoreNonFptrType t =
      case t of
        FunTy _ _ _ -> False
        PtrTo t' -> ignoreNonFptrType t'
        _ -> True
    gis = foldr extractGlobalFieldInits mempty (modGlobals m)

-- FIXME: One day push this hack down into the andersen analysis.
extractGlobalFieldInits :: Global -> HashMap (Type, Int) (HashSet Value) -> HashMap (Type, Int) (HashSet Value)
extractGlobalFieldInits gv acc = fromMaybe acc $ do
  (valValue -> ValStruct vs _) <- globalValue gv
  return $ foldr (addFieldInit (globalType gv)) acc (zip [0..] vs)
  where
    addFieldInit t (ix, v) =
      HM.insertWith HS.union (t, ix) (HS.singleton v)

-- Find all initializers of function types to global fields.  Make a map
-- of (struct type, field no) -> {initializers}
