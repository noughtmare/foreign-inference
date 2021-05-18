{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, RankNTypes #-}
{-# LANGUAGE ViewPatterns, DeriveGeneric, TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
-- | Identify function arguments that are *finalized*.  An argument is
-- finalized if, on every path, it is passed as a parameter to a
-- function that finalizes it *or* the argument is NULL.
--
-- The dataflow fact is a bit per argument that, if set, indicates
-- that the argument is neither finalized nor null.  The meet operator
-- is bitwise or.  This is actually implemented with sets and union.
-- The finalized arguments are those that are *NOT* in the set at the
-- end of the function.  This function need only consider normal
-- returns.  Functions with an unreachable return (due to exit,
-- longjmp, etc) are not finalizers.
module Foreign.Inference.Analysis.Finalize (
  FinalizerSummary,
  identifyFinalizers,
  automaticFinalizersForType,
  -- * Testing
  finalizerSummaryToTestFormat
  ) where

import GHC.Generics ( Generic )

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Lens', (%~), (.~), makeLenses )
import Control.Monad ( foldM )
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow
import LLVM.Analysis.NullPointers

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

-- | If an argument is finalized, it will be in the map with its
-- associated witnesses.  If no witnesses could be identified, the
-- witness list will simply be empty.
type SummaryType = HashMap Argument [Witness]
data FinalizerSummary =
  FinalizerSummary { _finalizerSummary :: SummaryType
                   , _finalizerDiagnostics :: Diagnostics
                   }
  deriving (Generic)

$(makeLenses ''FinalizerSummary)

instance Eq FinalizerSummary where
  (FinalizerSummary s1 _) == (FinalizerSummary s2 _) = s1 == s2

instance Semigroup FinalizerSummary where
  (<>) = mappend

instance Monoid FinalizerSummary where
  mempty = FinalizerSummary mempty mempty
  mappend (FinalizerSummary s1 d1) (FinalizerSummary s2 d2) =
    FinalizerSummary (HM.unionWith merge s1 s2) (mappend d1 d2)
    where
      merge l1 l2 = S.toList $ S.union (S.fromList l1) (S.fromList l2)

instance NFData FinalizerSummary where
  rnf = genericRnf

instance HasDiagnostics FinalizerSummary where
  diagnosticLens = finalizerDiagnostics

instance SummarizeModule FinalizerSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeFinalizerArgument

summarizeFinalizerArgument :: Argument
                              -> FinalizerSummary
                              -> [(ParamAnnotation, [Witness])]
summarizeFinalizerArgument a (FinalizerSummary m _) =
  case HM.lookup a m of
    Nothing -> []
    Just ws -> [(PAFinalize, ws)]

data FinalizerData =
  FinalizerData { moduleSummary :: FinalizerSummary
                , singleInitSummary :: IndirectCallSummary
                }

-- | Find all functions of one parameter that finalize the given type.
automaticFinalizersForType :: FinalizerSummary -> Type -> [Define]
automaticFinalizersForType (FinalizerSummary s _) t =
  filter (isSingleton . defArgs) funcs
  where
    isSingleton = (==1) . length
    args = HM.keys s
    compatibleArgs = filter ((t==) . argType) args
    funcs = map argDefine compatibleArgs

-- | The dataflow fact tracking things that are not finalizedOrNull
data FinalizerInfo =
  FinalizerInfo { _finalizedOrNull :: HashSet Argument
                , _finalizedWitnesses :: HashMap Argument (Set Witness)
                }
  deriving (Eq, Show)

$(makeLenses ''FinalizerInfo)

identifyFinalizers :: (FuncLike funcLike, HasDefine funcLike,
                       HasCFG funcLike, HasNullSummary funcLike)
                      => DependencySummary
                      -> IndirectCallSummary
                      -> Lens' compositeSummary FinalizerSummary
                      -> ComposableAnalysis compositeSummary funcLike
identifyFinalizers ds ics =
  composableAnalysisM runner finalizerAnalysis
  where
    runner a = runAnalysis a ds constData ()
    constData = FinalizerData mempty ics

-- | FIXME: To deal with finalizers called through function pointers,
-- a more sophisticated approach is required.  Paths are allowed to
-- not finalize IFF the function pointer doing the finalizing was NULL
-- on that path.  Example:
--
-- > if(mem) {
-- >   if(mem->free_func) {
-- >     mem->free_func(d);
-- >   }
-- > }
--
-- should be a reasonable finalizer body.  The approach will be to
-- track variables that are currently being tested for NULL; if those
-- variables are used to make a call through a function pointer, then
-- do a bit of magic in the meet function to allow this.
-- instance MeetSemiLattice FinalizerInfo where

meet :: FinalizerInfo -> FinalizerInfo -> FinalizerInfo
meet (FinalizerInfo s1 m1) (FinalizerInfo s2 m2) =
  FinalizerInfo { _finalizedOrNull = HS.intersection s1 s2
                , _finalizedWitnesses = HM.unionWith S.union m1 m2
                }

type Analysis = AnalysisMonad FinalizerData ()

-- FIXME: The result extraction from the dataflow analysis has to change.
-- Instead of looking at the unique exit node, look at the *return inst*.
-- Otherwise, calls to exit in error branches make functions into non-finalizers
-- when they otherwise might be.

finalizerAnalysis :: (FuncLike funcLike, HasDefine funcLike,
                      HasCFG funcLike, HasNullSummary funcLike)
                     => funcLike
                     -> FinalizerSummary
                     -> Analysis FinalizerSummary
finalizerAnalysis funcLike s@(FinalizerSummary summ _) = do
  -- Update the immutable data with the information we have gathered
  -- from the rest of the module so far.  We want to be able to access
  -- this in the Reader environment
  let envMod e = e { moduleSummary = s }
      univSet = HS.fromList $ filter isPointer (defArgs f)
      top = FinalizerInfo univSet mempty
      fact0 = FinalizerInfo mempty mempty
      analysis = fwdDataflowEdgeAnalysis top meet finalizerTransfer finalizerEdgeTransfer

  funcInfo <- analysisLocal envMod (dataflow funcLike analysis fact0)

  let FinalizerInfo finalized witnesses = dataflowResult funcInfo
      attachWitness a = HM.insert a (S.toList (HM.lookupDefault mempty a witnesses))
      newInfo = HS.foldr attachWitness mempty finalized
  -- Note, we perform the union with newInfo first so that any
  -- repeated keys take their value from what we just computed.  This
  -- is important for processing SCCs in the call graph, where a
  -- function may be visited more than once.  We always want the most
  -- up-to-date info.
  return $! (finalizerSummary .~ newInfo `HM.union` summ) s
  where
    f = getDefine funcLike

finalizerEdgeTransfer :: FinalizerInfo
                         -> Stmt
                         -> Analysis [(BasicBlock, FinalizerInfo)]
finalizerEdgeTransfer info i = return $ fromMaybe [] $ do
  (nullBlock, val, _) <- branchNullInfo i
  -- On the NULL block, insert val
  return $ [(nullBlock, addNullArg val info)]

finalizerTransfer :: FinalizerInfo
                     -> Stmt
                     -> Analysis FinalizerInfo
finalizerTransfer info i =
  case stmtInstr i of
    Call _ _ calledFunc args ->
      callTransfer i (stripBitcasts calledFunc) args info
    Invoke _ calledFunc args _ _ ->
      callTransfer i (stripBitcasts calledFunc) args info
    _ -> return info

addNullArg :: Value -> FinalizerInfo -> FinalizerInfo
addNullArg v info = fromMaybe info $ do
  ValIdent (IdentValArgument arg) <- pure (valValue v)
  return $ (finalizedOrNull %~ HS.insert arg) info

callTransfer :: Stmt -> Value -> [Value] -> FinalizerInfo -> Analysis FinalizerInfo
callTransfer callInst v as info =
  case valueContent' v of
    ValInstr Load{} -> do
      sis <- analysisEnvironment singleInitSummary
      let f = bbDefine (stmtBasicBlock callInst)
          fv = toValue f
          finits = filter (/=fv) $ indirectCallInitializers sis v
          xfer initializer = callTransfer callInst initializer as info
      minfos <- mapM xfer finits
      case minfos of
        [] -> return info
        info1:infos -> do
          -- If there is more than one static initializer for the
          -- function pointer being called, treat it as a finalizer
          -- IFF all of the initializers agree and finalize the same
          -- argument.
          case all (==info1) infos of
            True -> return info1
            False -> return info
    _ -> do
      modSumm <- analysisEnvironment moduleSummary
      foldM (checkArg modSumm) info indexedArgs
  where
    indexedArgs = zip [0..] as
    -- FIXME: Try the following variation: in an SCC, analyze each function
    -- in isolation (no function sees results from the others).  Then, this
    -- transfer function would assume that functions with no summary do finalize
    -- their arguments.  After each function in an SCC is analyzed, then combine
    -- all of the results and move on to iteration two.  This would pick up
    -- mutually-recursive finalizers.
    checkArg ms acc (ix, valValue . valueContent' -> ValIdent (IdentValArgument a)) = do
      attrs <- lookupArgumentSummaryList ms v ix
      case PAFinalize `elem` attrs of
        False -> return acc
        True -> return $! addArgWithWitness a callInst "finalized" acc
    checkArg _ acc _ = return acc


-- Perhaps modify the function call transfer here?  If we are calling a
-- finalizer on a value that we know IS NOT NULL,

addArgWithWitness :: Argument -> Stmt -> String -> FinalizerInfo -> FinalizerInfo
addArgWithWitness a i reason (FinalizerInfo s m) =
  let w = Witness i reason
  in FinalizerInfo { _finalizedOrNull = HS.insert a s
                   , _finalizedWitnesses = HM.insertWith S.union a (S.singleton w) m
                   }

-- Helpers

isPointer :: (IsValue a) => a -> Bool
isPointer v =
  case valType (toValue v) of
    (PtrTo _) -> True
    _ -> False


-- Testing

finalizerSummaryToTestFormat :: FinalizerSummary -> Map String (Set String)
finalizerSummaryToTestFormat (FinalizerSummary m _) = convert m
  where
    convert = foldr (addElt . toFuncNamePair) mempty . HM.keys
    addElt (f, a) = MS.insertWith S.union f (S.singleton a)
    toFuncNamePair arg =
      let f = argDefine arg
      in (prettySymbol (defName f), argName arg)
