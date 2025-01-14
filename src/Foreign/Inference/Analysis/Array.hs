{-# LANGUAGE ViewPatterns, RankNTypes, DeriveGeneric, TemplateHaskell #-}
-- | This module defines the Array Analysis from the PLDI 2009 paper.
--
-- The analysis identifies which pointer parameters of a function are
-- used as arrays in that function (or any callees).  The analysis is
-- flow insensitive and works by examining chains of GetElementPtr and
-- Load instructions to reconstruct the shape of arrays that are
-- accessed.
module Foreign.Inference.Analysis.Array (
  -- * Interface
  ArraySummary,
  identifyArrays,
  -- * Testing
  arraySummaryToTestFormat
  ) where

import GHC.Generics ( Generic )

import Control.Arrow
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Lens', (.~), makeLenses )
import Control.Monad ( foldM )
import Data.List ( foldl' )
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as M
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Internal.FlattenValue

-- import Debug.Trace
-- debug' = flip trace

-- | The real type of the summary (without the wrapper that is exposed
-- to clients).
type SummaryType = HashMap Argument Int

-- | Summarize the array parameters in the module.  This maps each
-- array argument to its inferred dimensionality.
-- newtype ArraySummary = APS SummaryType
data ArraySummary =
  ArraySummary { _arraySummary :: SummaryType
               , _arrayDiagnostics :: Diagnostics
               }
  deriving (Generic)

$(makeLenses ''ArraySummary)

instance Eq ArraySummary where
  (ArraySummary s1 _) == (ArraySummary s2 _) = s1 == s2

instance Semigroup ArraySummary where
  (<>) = mappend

instance Monoid ArraySummary where
  mempty = ArraySummary M.empty mempty
  mappend (ArraySummary s1 d1) (ArraySummary s2 d2) =
    ArraySummary (M.unionWith max s1 s2) (mappend d1 d2)

instance NFData ArraySummary where
  rnf = genericRnf

instance HasDiagnostics ArraySummary where
  diagnosticLens = arrayDiagnostics

instance SummarizeModule ArraySummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeArrayArgument

summarizeArrayArgument :: Argument -> ArraySummary -> [(ParamAnnotation, [Witness])]
summarizeArrayArgument a (ArraySummary summ _) =
  case M.lookup a summ of
    Nothing -> []
    Just depth -> [(PAArray depth, [])]

type Analysis = AnalysisMonad () ()

-- | A data type to capture uses of pointers in array contexts.  These
-- are accumulated in one pass over the function and then used to
-- reconstruct the shapes of arrays in the tracing functions.
data PointerUse = IndexOperation Value [Value]
                | CallArgument Int
                deriving (Show)

identifyArrays :: (FuncLike funcLike, HasDefine funcLike)
                  => DependencySummary
                  -> Lens' compositeSummary ArraySummary
                  -> ComposableAnalysis compositeSummary funcLike
identifyArrays ds =
  composableAnalysisM runner arrayAnalysis
  where
    runner a = runAnalysis a ds () ()

-- | The summarization function - add a summary for the current
-- Function to the current summary.  This function collects all of the
-- base+offset pairs and then uses @traceFromBases@ to reconstruct
-- them.
arrayAnalysis :: (FuncLike funcLike, HasDefine funcLike)
                 => funcLike -> ArraySummary -> Analysis ArraySummary
arrayAnalysis funcLike a@(ArraySummary summary _) = do
  basesAndOffsets <- mapM (isArrayDeref a) insts
--  let basesAndOffsets = map (isArrayDeref ds a) insts
  let baseResultMap = foldr (\itm acc -> foldr addDeref acc itm) M.empty basesAndOffsets
      summary' = M.foldlWithKey' (traceFromBases baseResultMap) summary baseResultMap
  return $! (arraySummary .~ summary') a
  where
    f = getDefine funcLike
    insts = concatMap bbStmts (defBody f)
    addDeref (base, use) = M.insertWith (++) base [use]

-- | Examine a GetElementPtr instruction result.  If the base is an
-- argument, trace its access structure (using the @baseResultMap@ via
-- @traceBackwards@) and record the dimensions in the summary.
--
-- Otherwise, just pass the summary along and try to find the next
-- access.
traceFromBases :: HashMap Value [PointerUse]
                  -> SummaryType
                  -> Value
                  -> [PointerUse]
                  -> SummaryType
traceFromBases baseResultMap summary base uses =
  -- FIXME: This test of argumentness needs to be extended to take
  -- into account PHI nodes (also selects)
  case valValue (valueContent' base) of
    ValIdent (IdentValArgument a) ->
      let depth = maximum $ map dispatchTrace uses
      in addToSummary depth a summary
    _ -> summary
  where
    dispatchTrace (IndexOperation result _) =
      traceBackwards baseResultMap result 1
    dispatchTrace (CallArgument depth) = depth

-- | Update the summary for an argument with a depth.
--
-- The function always keeps the *maximum* array depth it discovers
-- (i.e., inserting an array depth of 1 for an argument that is
-- already recorded as having depth 2 will not make any changes to the
-- summary).
addToSummary :: Int -> Argument -> SummaryType -> SummaryType
addToSummary depth arg =
  M.insertWith max arg depth


traceBackwards :: HashMap Value [PointerUse] -> Value -> Int -> Int
traceBackwards baseResultMap result depth =
  -- Is the current result used as the base of an indexing operation?
  -- If so, that adds a level of array wrapping.
  case M.lookup result baseResultMap of
    Nothing -> depth
    Just uses -> maximum (map dispatchTrace uses)
  where
    dispatchTrace use =
      case use of
        IndexOperation result' _ -> traceBackwards baseResultMap result' (depth + 1)
        CallArgument d -> depth + d

isArrayDeref :: ArraySummary
                -> Stmt
                -> Analysis [(Value, PointerUse)]
isArrayDeref summ inst =
  case valueContent' inst of
    ValInstr (Load (ValInstr (GEP _ base idxs)) _ _) ->
      return $ handleGEP idxs base
    ValInstr (Store (ValInstr (GEP _ base idxs)) _ _ _) ->
      return $ handleGEP idxs base
    ValInstr (CmpXchg _ _ (ValInstr (GEP _ base idxs)) _ _ _ _ _) ->
      return $ handleGEP idxs base
    ValInstr (AtomicRW _ _ (ValInstr (GEP _ base idxs)) _ _ _) ->
      return $ handleGEP idxs base
    ValInstr (Call _ _ f args) ->
      let indexedArgs = zip [0..] args
      in foldM (collectArrayArgs summ f) [] (concatMap expand indexedArgs)
    ValInstr (Invoke _ f args _ _) ->
      let indexedArgs = zip [0..] args
      in foldM (collectArrayArgs summ f) [] (concatMap expand indexedArgs)
    _ -> return []
  where
    expand (ix, a) = zip (repeat ix) (flattenValue a)
    handleGEP idxs base =
      let flatVals = flattenValue base
      in foldl' (buildArrayDeref inst idxs) [] flatVals

buildArrayDeref :: Stmt -> [Value] -> [(Value, PointerUse)] -> Value -> [(Value, PointerUse)]
buildArrayDeref inst idxs acc base =
  case idxs of
    [] -> error ("Foreign.Inference.Analysis.buildArrayDeref: GEP with no indices: " ++ show inst)
    [_] -> (base, IndexOperation (toValue inst) idxs) : acc
    (valValue . valueContent' -> ValInteger 0) : _ -> acc
    _ -> (base, IndexOperation (toValue inst) idxs ) : acc

-- | If the argument is an array (according to either the module
-- summary or the dependency summary), make a CallArgument tag for it.
-- Only bother inspecting direct calls.  Information gained from
-- indirect calls is unreliable since we don't have all possible
-- callees, even with a very powerful points-to analysis.
collectArrayArgs :: ArraySummary
                    -> Value
                    -> [(Value, PointerUse)]
                    -> (Int, Value)
                    -> Analysis [(Value, PointerUse)]
collectArrayArgs summ callee lst (ix, arg) = do
  annots <- lookupArgumentSummaryList summ callee ix
  case filter isArrayAnnot annots of
    [] -> return lst
    [PAArray depth] -> return $ (arg, CallArgument depth) : lst
    _ -> do
      emitError Nothing "Array.collectArrayArgs" "Summary should only produce singleton or empty lists"
      return lst


isArrayAnnot :: ParamAnnotation -> Bool
isArrayAnnot (PAArray _) = True
isArrayAnnot _ = False


-- Testing

arraySummaryToTestFormat :: ArraySummary -> Map (String, String) Int
arraySummaryToTestFormat (ArraySummary summ _) =
  Map.fromList $ map (first argToString) $ M.toList summ
  where
    argToString a =
      let f = argDefine a
      in (prettySymbol (defName f), argName a)
