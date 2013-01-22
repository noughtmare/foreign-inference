{-# LANGUAGE TemplateHaskell, DeriveGeneric, ViewPatterns #-}
{-# LANGUAGE RankNTypes #-}
-- | An analysis to identify @Symbolic Access Paths@ for each function
-- in a Module.
module Foreign.Inference.Analysis.SAP (
  SAPSummary,
  identifySAPs,
  -- * Testing
  sapReturnResultToTestFormat,
  sapArgumentResultToTestFormat
  ) where

import GHC.Generics ( Generic )

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Simple, makeLenses, (%~), (.~), (^.) )
import Control.Monad ( foldM )
import qualified Data.Foldable as F
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe, mapMaybe )
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Safe.Failure ( at )

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

-- FIXME: This could be extended with a FinalizesPath constructor
-- to record transitive field finalizers
data AugmentedAccessPath = WritePath !Int AbstractAccessPath !Int
                           -- ^ Argument being stored into, Access
                           -- path into that argument, and the
                           -- argument being stored.
                         deriving (Eq, Ord, Show, Generic)

instance NFData AugmentedAccessPath where
  rnf = genericRnf

type ReturnPath = (Int, AbstractAccessPath)

data SAPSummary =
  SAPSummary { _sapReturns :: Map Function (Set ReturnPath)
               -- ^ The return paths for each function
             , _sapArguments :: Map Argument (Set AugmentedAccessPath)
               -- ^ Maps each Argument to the access paths it is
               -- stored into.
             , _sapDiagnostics :: Diagnostics
             }
  deriving (Generic)

$(makeLenses ''SAPSummary)

instance Eq SAPSummary where
  (SAPSummary r1 a1 _) == (SAPSummary r2 a2 _) =
    r1 == r2 && a1 == a2

instance Monoid SAPSummary where
  mempty = SAPSummary mempty mempty mempty
  mappend (SAPSummary r1 a1 d1) (SAPSummary r2 a2 d2) =
    SAPSummary (M.union r1 r2) (M.unionWith S.union a1 a2) (d1 `mappend` d2)

instance NFData SAPSummary where
  rnf = genericRnf

instance HasDiagnostics SAPSummary where
  diagnosticLens = sapDiagnostics

type Analysis = AnalysisMonad () ()

instance SummarizeModule SAPSummary where
  summarizeArgument _ _ = []
  summarizeFunction _ _ = []

identifySAPs :: (FuncLike funcLike, HasFunction funcLike)
                => DependencySummary
                -> Simple Lens compositeSummary SAPSummary
                -> ComposableAnalysis compositeSummary funcLike
identifySAPs ds lns =
  composableAnalysisM runner sapAnalysis lns
  where
    runner a = runAnalysis a ds () ()

-- | For non-void functions, first check the return instruction and
-- see if it is returning some access path.  Next, just iterate over
-- all stores.
--
-- At call intructions, extend callee paths that are passed some path
-- based on an argument.
sapAnalysis :: (FuncLike funcLike, HasFunction funcLike)
               => funcLike
               -> SAPSummary
               -> Analysis SAPSummary
sapAnalysis flike s =
  foldM (sapTransfer f) s (functionInstructions f)
  where
    f = getFunction flike

sapTransfer :: Function
               -> SAPSummary
               -> Instruction
               -> Analysis SAPSummary
sapTransfer f s i =
  case i of
    RetInst { retInstValue = Just (valueContent' ->
      InstructionC PhiNode { phiIncomingValues = (map fst -> ivs) })} ->
      foldM (returnValueTransfer f) s (valuesAsInsts ivs)
    RetInst { retInstValue = Just (valueContent' ->
      InstructionC SelectInst { selectTrueValue = tv, selectFalseValue = fv })} ->
      foldM (returnValueTransfer f) s (valuesAsInsts [tv, fv])
    RetInst { retInstValue = Just (valueContent' -> InstructionC ri) } ->
      returnValueTransfer f s ri

    -- We need to make an entry in sapArguments if we store an argument
    -- into some access path based on another argument
    --
    -- FIXME: If we are storing into the result of a callinst, check
    -- to see if that call has a summary that could be extended.
    StoreInst { storeValue = (valueContent' -> ArgumentC sv) } ->
      storeTransfer s i sv

    CallInst { callFunction = (valueContent' -> FunctionC callee)
             , callArguments = (map fst -> actuals) } ->
      foldM (callTransfer callee actuals) s (zip [0..] actuals)
    InvokeInst { invokeFunction = (valueContent' -> FunctionC callee)
               , invokeArguments = (map fst -> actuals) } ->
      foldM (callTransfer callee actuals) s (zip [0..] actuals)

    _ -> return s

-- | If we are calling a function that, as a side-effect, stores one
-- of its arguments into a field of another, we need to stitch
-- together the access paths (as in the transitive return call case).
-- This propagates information about the _store_ case to callers.
--
-- > void g(struct S *s, int *x) {
-- >   s->f1 = x;
-- > }
-- >
-- > void f(struct T *t, int *x) {
-- >   g(t->s, x);
-- > }
--
-- The summary for @g@ is produced by the _store_ case.  This function
-- produces the summary for @f@ based on the call to @g@.  This
-- function is called once for each actual argument to the call of @g@
-- by the top-level transfer function.
callTransfer :: Function
                -> [Value]
                -> SAPSummary
                -> (Int, Value)
                -> Analysis SAPSummary
callTransfer callee actuals s (argIx, actual) =
  return $ fromMaybe s $ do
    -- This formal is @x@ in @f@; it is a *formal* argument passed to
    -- @g@ as an *actual* parameter.
    formal <- fromValue actual
    calleeFormal <- functionParameters callee `at` argIx
    calleeFormalSumm <- M.lookup calleeFormal (s ^. sapArguments)
    -- We now have to extend each of the summaries for this argument.
    -- Each summary tells us which other actual this formal is stored
    -- into.
    let args' = F.foldr (augmentTransfer formal) (s ^. sapArguments) calleeFormalSumm
    return $ (sapArguments .~ args') s
  where
    -- Called once per summary for this argument.
    augmentTransfer formal (WritePath dstArg p _) argSumm =
      fromMaybe argSumm $ do
        baseActual <- actuals `at` dstArg
        case valueContent' baseActual of
          ArgumentC argActual -> do
            -- In this case, the actual argument is just an argument
            -- (could be considered a degenerate access path).  This
            -- is the case where an argument is passed-through to
            -- a function.
            --
            -- In the example, this would be the first argument to @g@
            -- if it was just an argument passed down to @g@ instead
            -- of a field access.
            let dstArg' = argumentIndex argActual
                wp = WritePath dstArg' p (argumentIndex formal)
            return $ M.insertWith S.union formal (S.singleton wp) argSumm
          _ -> do
            -- In this case, the actual argument is some field or
            -- array access.  That is @t->s@
            actualInst <- fromValue baseActual
            cap' <- accessPath actualInst
            -- @t@ in the example
            baseArg <- accessPathBaseArgument cap'
            let absPath = abstractAccessPath cap'
            -- Extend the summary from @g@ with the @t->s@ we just
            -- observed.
            p' <- absPath `appendAccessPath` p
            let formalIx = argumentIndex formal
                dstArg' = argumentIndex baseArg
                wp = WritePath dstArg' p' formalIx
            return $ M.insertWith S.union formal (S.singleton wp) argSumm

-- | If this StoreInst represents the store of an Argument into a
-- field of another argument, record that in the sapArguments summary.
--
-- > void f(struct S *s, struct Foo *foo) {
-- >   s->bar = foo;
-- > }
--
-- > WritePath 0 S.<0> 1
--
-- Argument 1 is stored into field zero of argument 0.
storeTransfer :: SAPSummary
                 -> Instruction -- ^ Store instruction
                 -> Argument -- ^ The argument being stored
                 -> Analysis SAPSummary
storeTransfer s storeInst storedArg =
  return $ maybe s addStore res
  where
    addStore res' =
      (sapArguments %~ M.insertWith S.union storedArg (S.singleton res')) s
    res = do
      -- This is @s->bar@
      cap <- accessPath storeInst
      -- And this is @s@
      base <- accessPathBaseArgument cap
      let absPath = abstractAccessPath cap
      return $! WritePath (argumentIndex base) absPath (argumentIndex storedArg)

-- | When the result of a call is returned, that call is known to
-- return an access path *into* one of its arguments.  What we need to
-- do here is figure out which of the callee's arguments the access
-- path uses (the Int the AAP is tagged with).
--
-- We then take the actual argument at that index and look up its
-- access path.  If that concrete access path is rooted at an
-- argument, we get the index of that argument and then append the
-- access paths.
transitiveReturnTransfer :: Function
                            -> SAPSummary
                            -> Function
                            -> [Value]
                            -> Analysis SAPSummary
transitiveReturnTransfer f s@(SAPSummary rs _ _) callee args =
  return $ fromMaybe s $ do
    rpaths <- M.lookup callee rs
    let trpaths = mapMaybe extendRPath $ S.toList rpaths
        rs' = foldr (M.insertWith S.union f) rs trpaths
    return $ (sapReturns .~ rs') s
  where
    extendRPath (ix, p) = do
      actual <- args `at` ix
      i <- fromValue actual
      cap <- accessPath i
      formal <- accessPathBaseArgument cap
      let absPath = abstractAccessPath cap
          tix = argumentIndex formal
      tp <- absPath `appendAccessPath` p
      return $ S.singleton (tix, tp)

-- FIXME: This could actually probably work on external functions,
-- too, if we are careful in representing access paths
returnValueTransfer :: Function
                       -> SAPSummary
                       -> Instruction
                       -> Analysis SAPSummary
returnValueTransfer f s CallInst { callArguments = (map fst -> args)
                                 , callFunction = (valueContent' -> FunctionC callee) } =
  transitiveReturnTransfer f s callee args
returnValueTransfer f s InvokeInst { invokeArguments = (map fst -> args)
                                   , invokeFunction = (valueContent' -> FunctionC callee) } =
  transitiveReturnTransfer f s callee args
returnValueTransfer f s i = return $ fromMaybe s $ do
  p <- accessPath i
  let absPath = abstractAccessPath p
      addArg aid =
        let v = S.singleton (aid, absPath)
        in (sapReturns %~ M.insertWith S.union f v) s
  case valueContent' (accessPathBaseValue p) of
    ArgumentC a -> return $ addArg (argumentIndex a)
    _ -> return s


valuesAsInsts :: [Value] -> [Instruction]
valuesAsInsts = mapMaybe toInst
  where
    toInst v =
      case valueContent' v of
        InstructionC i -> Just i
        _ -> Nothing

accessPathBaseArgument :: AccessPath -> Maybe Argument
accessPathBaseArgument p =
  case valueContent' (accessPathBaseValue p) of
    ArgumentC a -> return a
    _ -> Nothing

-- Testing

sapReturnResultToTestFormat :: SAPSummary -> Map String (Set (Int, String, [AccessType]))
sapReturnResultToTestFormat =
  M.fromList . map toTestFormat . M.toList . (^. sapReturns)
  where
    toTestFormat (f, s) =
      (identifierAsString (functionName f),
       S.map fromRetPath s)
    fromRetPath (ix, p) =
      (ix, show (abstractAccessPathBaseType p),
       abstractAccessPathComponents p)

sapArgumentResultToTestFormat :: SAPSummary -> Map (String, String) (Set (Int, String, [AccessType]))
sapArgumentResultToTestFormat =
  M.fromList . map toTestFormat . M.toList . (^. sapArguments)
  where
    toTestFormat (a, s) =
      let f = argumentFunction a
          p1 = (identifierAsString (functionName f),
                identifierAsString (argumentName a))
      in (p1, S.map fromPath s)
    fromPath (WritePath ix p _) =
      (ix, show (abstractAccessPathBaseType p),
       abstractAccessPathComponents p)