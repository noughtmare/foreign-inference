{-# LANGUAGE DeriveGeneric, TemplateHaskell, ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
module Foreign.Inference.Analysis.Transfer (
  TransferSummary,
  identifyTransfers
  ) where

import GHC.Generics ( Generic )

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( (%~), (.~), (^.), Simple, makeLenses )
import Control.Monad ( foldM )
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.PointsTo

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.IndirectCallResolver

import Debug.Trace
debug = flip trace

data TransferSummary = TransferSummary {
  _transferArguments :: Set Argument,
  _transferDiagnostics :: Diagnostics
  }
  deriving (Generic)

$(makeLenses ''TransferSummary)

instance Eq TransferSummary where
  (TransferSummary _ _) == (TransferSummary _ _) = True

instance Monoid TransferSummary where
  mempty = TransferSummary mempty mempty
  mappend (TransferSummary t1 d1) (TransferSummary t2 d2) =
    TransferSummary (t1 `mappend` t2) (d1 `mappend` d2)

instance NFData TransferSummary where
  rnf = genericRnf

instance HasDiagnostics TransferSummary where
  diagnosticLens = transferDiagnostics

instance SummarizeModule TransferSummary where
  summarizeFunction _ _ = []
  summarizeArgument a (TransferSummary t _)
    | S.member a t = [(PATransfer, [])]
    | otherwise = []


-- Algorithm:
--
-- In one pass, determine all of the *structure fields* that are
-- passed to a finalizer.  These are *owned* fields.  The shape
-- analysis bit will come later (to find finalized things that are
-- stored in "container-likes")
--
-- Maybe we can remove the need for some shape analysis by looking at
-- dependence.
--
-- > void foo(bar * baz) {
-- >   while(hasNext(baz->quux)) {
-- >     q = next(&baz->quux);
-- >     free_quux(q);
-- >   }
-- > }
--
-- In a second pass, find all of the arguments that flow into those
-- owned fields and mark them as Transferred.  Again, this will need
-- to be aware of the pseudo-shape analysis results (i.e., this
-- parameter ends up linked into this data structure via this field
-- after this call).  This pass will need to reach a fixed point.
--
-- At the end of the day, this will be simpler than the escape
-- analysis since we do not need to track fields of arguments or
-- anything of that form.
--
-- This could additionally depend on the ref count analysis and just
-- strip off transfer tags from ref counted types.

identifyTransfers :: (HasFunction funcLike)
                     => [funcLike]
                     -> DependencySummary
                     -> IndirectCallSummary
                     -> compositeSummary
                     -> Simple Lens compositeSummary FinalizerSummary
                     -> Simple Lens compositeSummary TransferSummary
                     -> compositeSummary
identifyTransfers funcLikes ds pta p1res flens tlens =
  (tlens .~ res) p1res
  where
    res = runAnalysis a ds () ()
    finSumm = p1res ^. flens
    trSumm = p1res ^. tlens
    a = do
      ownedFields <- foldM (identifyOwnedFields pta finSumm) mempty funcLikes
      transferedParams <- foldM (identifyTransferredArguments pta ownedFields) trSumm funcLikes
      return () `debug` show ownedFields
      return transferedParams

type Analysis = AnalysisMonad () ()

identifyTransferredArguments :: (HasFunction funcLike)
                                => IndirectCallSummary
                                -> Set AbstractAccessPath
                                -> TransferSummary
                                -> funcLike
                                -> Analysis TransferSummary
identifyTransferredArguments pta ownedFields trSumm flike =
  foldM checkTransfer trSumm (functionInstructions f)
  where
    f = getFunction flike
    args = functionParameters f
    checkTransfer s@(TransferSummary t d) i =
      case i of
        StoreInst { storeAddress = sa, storeValue = (valueContent' -> ArgumentC sv) }
          | sv `elem` args -> return $ fromMaybe s $ do
            acp <- accessPath i
            let absPath = abstractAccessPath acp
            case S.member absPath ownedFields of
              True -> return $! (transferArguments %~ S.insert sv) s
              False -> return s
          | otherwise -> return s
        CallInst { callFunction = callee, callArguments = (map fst -> args) } ->
          transitiveTransfers callee args
        InvokeInst { invokeFunction = callee, invokeArguments = (map fst -> args) } ->
          transitiveTransfers callee args
        _ -> return s
    transitiveTransfers callee args = do
      return undefined

-- | Add any field passed to a known finalizer to the accumulated Set.
--
-- This will eventually need to incorporate shape analysis results.
-- It will also need to distinguish somehow between fields that are
-- finalized and elements of container fields that are finalized.
identifyOwnedFields :: (HasFunction funcLike)
                       => IndirectCallSummary
                       -> FinalizerSummary
                       -> Set AbstractAccessPath
                       -> funcLike
                       -> Analysis (Set AbstractAccessPath)
identifyOwnedFields pta finSumm ownedFields funcLike =
  foldM checkFinalize ownedFields insts
  where
    insts = functionInstructions (getFunction funcLike)
    checkFinalize acc i =
      case i of
        CallInst { callFunction = cf, callArguments = (map fst -> args) } ->
          checkCall cf args acc
        InvokeInst { invokeFunction = cf, invokeArguments = (map fst -> args) } ->
          checkCall cf args acc
        _ -> return acc
    checkCall cf args acc = do
      let nargs = length args
      mfinIx <- foldM (isFinalizer nargs) Nothing (pointsTo pta cf)
      case mfinIx of
        Nothing -> return acc
        Just finIx ->
          let actual = args !! finIx
          in case valueContent' actual of
            InstructionC i -> return $ fromMaybe acc $ do
              accPath <- accessPath i
              let absPath = abstractAccessPath accPath
              return $ S.insert absPath acc
            _ -> return acc
    isFinalizer _ a@(Just _) _ = return a
    isFinalizer nargs Nothing callee =
      foldM (formalHasFinalizeAnnot callee) Nothing [0..(nargs-1)]
    formalHasFinalizeAnnot _ a@(Just _) _ = return a
    formalHasFinalizeAnnot callee Nothing argIx = do
      annots <- lookupArgumentSummaryList finSumm callee argIx
      if PAFinalize `elem` annots
        then return (Just argIx)
        else return Nothing
