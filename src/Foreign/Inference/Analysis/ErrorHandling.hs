{-# LANGUAGE ViewPatterns, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric, PatternGuards #-}
-- | This analysis attempts to automatically identify error-handling
-- code in libraries.
--
-- The error laws are:
--
--  * (Transitive error) If function F returns the result of calling
--    callee C directly, and C has error handling pattern P, then F
--    has error handling pattern P.
--
--  * (Known error) If function F checks the result of calling C for
--    an error condition and performs some action ending in a constant
--    integer error return code, that is error handling code.  Actions
--    are assigning to globals and calling functions. (Note: may need
--    to make this a non-zero return).
--
--  * (Generalize return) If F calls any (all?) of the functions in an
--    error descriptor and then returns a constant int I, I is a new
--    error code used in this library.
--
--  * (Generalize action) If a function F returns a constant int I
--    that is the return code for a known error handling pattern, then
--    the functions called on that branch are a new error handling
--    pattern.
module Foreign.Inference.Analysis.ErrorHandling (
  ErrorSummary,
  identifyErrorHandling,
  ) where

import GHC.Generics

import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Monad ( foldM, liftM, mzero, when )
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import qualified Data.Foldable as F
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.IntMap ( IntMap )
import qualified Data.IntMap as IM
import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NEL
import Data.Maybe ( fromMaybe )
import Data.Monoid
import Data.SBV
import Data.Set ( Set )
import qualified Data.Set as S
import System.IO.Unsafe ( unsafePerformIO )

import LLVM.Analysis
import LLVM.Analysis.BlockReturnValue
import LLVM.Analysis.CDG
import LLVM.Analysis.CFG

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface
import Foreign.Inference.Analysis.IndirectCallResolver

{-import Text.Printf-}
{-import Debug.Trace-}
{-debug :: a -> String -> a-}
{-debug = flip trace-}

-- | An ErrorDescriptor describes a site in the program handling an
-- error (along with a witness).
data ErrorDescriptor =
  ErrorDescriptor { errorActions :: Set ErrorAction
                  , errorReturns :: ErrorReturn
                  , errorWitnesses :: [Witness]
                  }
  deriving (Eq, Ord, Generic, Show)

instance NFData ErrorDescriptor where
  rnf = genericRnf

-- | The error summary is the type exposed to callers, mapping each
-- function to its error handling methods.
type SummaryType = HashMap Function (Set ErrorDescriptor)
data ErrorSummary = ErrorSummary SummaryType Diagnostics
                  deriving (Generic)

instance Eq ErrorSummary where
  (ErrorSummary s1 _) == (ErrorSummary s2 _) = s1 == s2

instance Monoid ErrorSummary where
  mempty = ErrorSummary mempty mempty
  mappend (ErrorSummary m1 d1) (ErrorSummary m2 d2) =
    ErrorSummary (HM.union m1 m2) (mappend d1 d2)

instance NFData ErrorSummary where
  rnf = genericRnf

-- This is a manual lens implementation as described in the lens
-- package.
instance HasDiagnostics ErrorSummary where
  diagnosticLens f (ErrorSummary s d) =
    fmap (\d' -> ErrorSummary s d') (f d)

data ErrorData =
  ErrorData { indirectCallSummary :: IndirectCallSummary
            }

-- | This is the data we want to bootstrap through the two
-- generalization rules
data ErrorState =
  ErrorState { errorCodes :: Set Int
             , errorFunctions :: Set String
             , successModel :: HashMap Function (Set Int)
             }

instance Monoid ErrorState where
  mempty = ErrorState mempty mempty mempty
  mappend (ErrorState c1 f1 s1) (ErrorState c2 f2 s2) =
    ErrorState { errorCodes = c1 `mappend` c2
               , errorFunctions = f1 `mappend` f2
               , successModel = HM.unionWith S.union s1 s2
               }


type Analysis = AnalysisMonad ErrorData ErrorState

identifyErrorHandling :: (HasFunction funcLike, HasBlockReturns funcLike,
                          HasCFG funcLike, HasCDG funcLike)
                         => [funcLike]
                         -> DependencySummary
                         -> IndirectCallSummary
                         -> ErrorSummary
identifyErrorHandling funcLikes ds ics =
  runAnalysis analysis ds roData mempty
  where
    roData = ErrorData ics
    analysis = do
      res <- fixAnalysis mempty
--      return () `debug` errorSummaryToString res
      return $ ErrorSummary res mempty
    fixAnalysis res = do
      res' <- foldM errorAnalysis res funcLikes
      if res == res' then return res
        else fixAnalysis res'

-- errorSummaryToString = unlines . map entryToString . HM.toList
--   where
--     entryToString (f, descs) = identifierAsString (functionName f) ++ ": " ++ show descs

instance SummarizeModule ErrorSummary where
  summarizeArgument _ _ = []
  summarizeFunction f (ErrorSummary summ _) = fromMaybe [] $ do
    fsumm <- HM.lookup f summ
    descs <- NEL.nonEmpty (F.toList fsumm)
    let retcodes = unifyReturnCodes descs
        ws = concatMap errorWitnesses (NEL.toList descs)
    case unifyErrorActions descs of
      Nothing -> return [(FAReportsErrors mempty retcodes, ws)]
      Just uacts -> return [(FAReportsErrors uacts retcodes, ws)]

-- | FIXME: Prefer error actions of size one (should discard extraneous
-- actions like cleanup code).
unifyErrorActions :: NonEmpty ErrorDescriptor -> Maybe (Set ErrorAction)
unifyErrorActions d0 = foldr unifyActions (Just d) ds
  where
    (d:|ds) = fmap errorActions d0
    unifyActions _ Nothing = Nothing
    unifyActions s1 acc@(Just s2)
      | S.size s1 == 1 && S.size s2 /= 1 = Just s1
      | s1 == s2 = acc
      | otherwise = Nothing

-- | Merge all return values; if ints and ptrs are mixed, prefer the
-- ints
unifyReturnCodes :: NonEmpty ErrorDescriptor -> ErrorReturn
unifyReturnCodes = F.foldr1 unifyReturns . fmap errorReturns
  where
    unifyReturns (ReturnConstantInt is1) (ReturnConstantInt is2) =
      ReturnConstantInt (is1 `S.union` is2)
    unifyReturns (ReturnConstantPtr is1) (ReturnConstantPtr is2) =
      ReturnConstantPtr (is1 `S.union` is2)
    unifyReturns (ReturnConstantPtr _) r@(ReturnConstantInt _) = r
    unifyReturns r@(ReturnConstantInt _) (ReturnConstantPtr _) = r


errorAnalysis :: (HasFunction funcLike, HasBlockReturns funcLike,
                  HasCFG funcLike, HasCDG funcLike)
              => SummaryType -> funcLike -> Analysis SummaryType
errorAnalysis summ funcLike =
  foldM (errorsForBlock funcLike) summ (functionBody f)
  where
    f = getFunction funcLike

-- | Find the error handling code in this block
errorsForBlock :: (HasFunction funcLike, HasBlockReturns funcLike,
                   HasCFG funcLike, HasCDG funcLike)
               => funcLike
               -> SummaryType
               -> BasicBlock
               -> Analysis SummaryType
errorsForBlock funcLike s bb = do
  takeFirst s [ reportsSuccess funcLike s bb
              , handlesKnownError funcLike s bb
              , matchActionAndGeneralizeReturn funcLike s bb
              , matchReturnAndGeneralizeAction funcLike s bb
              , returnsTransitiveError funcLike s bb
              ]
  where
    takeFirst :: (Monad m) => a -> [m (Either a a)] -> m a
    takeFirst def [] = return def
    takeFirst _ (act:rest) = do
      res <- act
      case res of
        Left def' -> takeFirst def' rest
        Right res' -> return res'

-- | If the function transitively returns errors, record them in the
-- error summary.  Errors are only transitive if they are unhandled in
-- this function.  For example, consider the following code:
--
-- > bs = read(..);
-- > if(bs < 0) {
-- >   setError(..);
-- >   return -20;
-- > }
-- >
-- > return bs;
--
-- Here, we do /not/ want to say that this function returns a
-- transitive error, even though the result of @read@ is one of its
-- return values.  The error code (bs == -1) is handled in the
-- conditional, so only non-error values can be returned (except where
-- the error was converted into an application-specific error code).
--
-- This decision is made with a call to the theorem prover, taking in
-- to account all of the conditions that currently hold when the value
-- must be returned.  See the 'relevantInducedFacts' function for
-- details.
returnsTransitiveError :: (HasFunction funcLike, HasBlockReturns funcLike,
                           HasCFG funcLike, HasCDG funcLike)
                       => funcLike
                       -> SummaryType
                       -> BasicBlock
                       -> Analysis (Either SummaryType SummaryType)
returnsTransitiveError funcLike summ bb
  | Just rv <- blockReturn brs bb = do
    ics <- analysisEnvironment indirectCallSummary
    case ignoreCasts rv of
      InstructionC i@CallInst { callFunction = callee } -> do
        let priorFacts = relevantInducedFacts funcLike bb i
            callees = callTargets ics callee
        liftM Right $ foldM (recordTransitiveError i priorFacts) summ callees
      _ -> return (Left summ)
  | otherwise = return (Left summ)
  where
    f = getFunction funcLike
    brs = getBlockReturns funcLike
    recordTransitiveError i priors s callee = do
      let w = Witness i "transitive error"
      fsumm <- lookupFunctionSummaryList (ErrorSummary s mempty) callee
      maybe (return s) (addErrorDescriptor f s) $ do
        FAReportsErrors errActs eret <- F.find isErrRetAnnot fsumm
        rvs <- intReturnsToList eret
        -- See Note [Transitive Returns with Conditions]
        case null priors of
          True -> return $! ErrorDescriptor errActs eret [w]
          False -> do
            let rvs' = foldr (addUncaughtErrors priors) mempty rvs
            return $! ErrorDescriptor errActs (ReturnConstantInt rvs') [w]


addErrorDescriptor :: Function -> SummaryType -> ErrorDescriptor
                   -> Analysis SummaryType
addErrorDescriptor f s d =
  return $ HM.insertWith S.union f (S.singleton d) s

-- | Check an error code @rc@ against all relevant conditions that are
-- active at the current program point.  If @rc@ has not been handled
-- by a different branch, add it to the list of error codes that could
-- be returned here.
--
-- Effectively, this filters out codes that are handled by other
-- branches and cannot be returned here.
addUncaughtErrors :: [SInt32 -> SBool] -> Int -> Set Int -> Set Int
addUncaughtErrors priors rc acc
  | not (null priors) && isSat formula = S.insert rc acc
  | otherwise = acc
  where
    formula (x :: SInt32) = x .== fromIntegral rc &&& bAll ($x) priors

intReturnsToList :: ErrorReturn -> Maybe [Int]
intReturnsToList er =
  case er of
    ReturnConstantInt is -> return $ S.toList is
    _ -> Nothing

-- | Try to generalize (learn new error codes) based on known error functions
-- that are called in this block.  If the block calls a known error function
-- and then returns a constant int, that is a new error code.
--
-- NOTE: It may be better to only generalize from error reporting functions
-- that modify a field of one of their arguments.  Just printing does not seem
-- to be entirely reliable.  On the other hand, some libraries just print.
--
-- An explicit model of success might help here.  If we can see that we are on
-- a success branch, don't try to generalize an error return.
matchActionAndGeneralizeReturn :: (HasFunction funcLike, HasBlockReturns funcLike,
                                   HasCFG funcLike, HasCDG funcLike)
                               => funcLike
                               -> SummaryType
                               -> BasicBlock
                               -> Analysis (Either SummaryType SummaryType)
matchActionAndGeneralizeReturn funcLike s bb = do
  fs <- learnedErrorFunctions
  -- If this basic block calls any functions in the errFuncs set, then use
  -- branchToErrorDescriptor f bb to compute a new error
  -- descriptor and then add the return value to the errCodes set.
  res <- runMaybeT $ do
    edesc <- branchToErrorDescriptor funcLike bb
    FunctionCall ecall _ <- liftMaybe $ F.find (isErrorFuncCall fs) (errorActions edesc)
    case errorReturns edesc of
      ReturnConstantPtr _ -> fail "Ptr return"
      ReturnConstantInt is -> do
        let ti = basicBlockTerminatorInstruction bb
            w = Witness ti ("Called " ++ ecall)
            d = edesc { errorWitnesses = [w] }
            -- Only learn new error codes if they are not 1/0
            --
            -- UPDATE: this hack is probably obsolete now that we are learning
            -- "success" codes.
            --
            -- FIXME: Maybe we should consult the success model and try not to
            -- generalize from any of those error codes?
  --          is' = S.filter (\c -> c > 1 || c < 0) is
        return (d, is)
  case res of
    Nothing -> return $ Left s
    Just (d, is) -> do
      addDesc <- addGeneralizedFailReturn funcLike is
      case addDesc of
        True -> liftM Right $ addErrorDescriptor f s d
        False -> liftM Left $ removeImprobableErrors f s d
  where
    f = getFunction funcLike

-- | Add error codes we have generalized based on an error reporting function.
-- There is an additional check: if we are about to add a value we know is
-- return on /success/ in this function, just skip it.  Generalization is less
-- powerful than direct observations (i.e., 3 is returned on success).
--
-- Additionally, remove instances of the success value that ended up in the
-- error code set.
addGeneralizedFailReturn :: (HasFunction funcLike)
                         => funcLike
                         -> Set Int
                         -> Analysis Bool
addGeneralizedFailReturn funcLike is = do
  st <- analysisGet
  let sucMod = successModel st
      ecodes' = errorCodes st `S.union` is
  case HM.lookup f sucMod of
    Nothing -> do
      analysisPut $ st { errorCodes = ecodes' }
      return True
    Just fsmod -> do
      analysisPut $ st { errorCodes = ecodes' `S.difference` fsmod }
      -- If there are no successes in ecodes', then we can safely generalize.
      -- Otherwise, this was a bogus generalization.
      return $! S.null (fsmod `S.intersection` ecodes')
  where
    f = getFunction funcLike

-- | Match a known error return and try to find new actions based on that.
matchReturnAndGeneralizeAction :: (HasFunction funcLike, HasBlockReturns funcLike,
                                   HasCFG funcLike, HasCDG funcLike)
                               => funcLike
                               -> SummaryType
                               -> BasicBlock
                               -> Analysis (Either SummaryType SummaryType)
matchReturnAndGeneralizeAction funcLike s bb = do
  ecodes <- learnedErrorCodes
  res <- runMaybeT $ do
    edesc <- branchToErrorDescriptor funcLike bb
    case errorReturns edesc of
      ReturnConstantPtr _ -> fail "Ptr return"
      ReturnConstantInt is
        | S.null (is `S.intersection` ecodes) ->
          fail "No known error code"
        | otherwise -> do
          let ti = basicBlockTerminatorInstruction bb
              w = Witness ti ("Returned " ++ show is)
              d = edesc { errorWitnesses = [w] }
          singleFunc <- singleFunctionErrorAction (errorActions edesc)
          learnErrorFunction singleFunc
          return d -- FIXME learn from d (the decomposition of the descriptor
                   -- can be pushed down
  case res of
    Nothing -> return $ Left s
    Just d -> liftM Right $ addErrorDescriptor f s d
--      return $ Right $! HM.insertWith S.union f (S.singleton d) s
  where
    f = getFunction funcLike

singleFunctionErrorAction :: Set ErrorAction -> MaybeT Analysis String
singleFunctionErrorAction acts =
  case filter isFuncallAct (S.toList acts) of
    [FunctionCall fname _] -> return fname
    _ -> fail "Not a singleton function call action"

learnErrorFunction :: String -> MaybeT Analysis ()
learnErrorFunction funcName = do
  st <- lift analysisGet
  let fs' = S.insert funcName (errorFunctions st)
  lift $ analysisPut st { errorFunctions = fs' }

-- | Return all of the error codes we have already learned.
--
-- NOTE: This is one place where we could filter out known "success codes".
learnedErrorCodes :: Analysis (Set Int)
learnedErrorCodes = liftM errorCodes analysisGet

learnedErrorFunctions :: Analysis (Set String)
learnedErrorFunctions = liftM errorFunctions analysisGet

-- | In this case, the basic block is handling a known error and turning it
-- into an integer return code (possibly while performing some other
-- relevant error-reporting actions).
handlesKnownError :: (HasFunction funcLike, HasBlockReturns funcLike,
                      HasCFG funcLike, HasCDG funcLike)
                  => funcLike
                  -> SummaryType
                  -> BasicBlock
                  -> Analysis (Either SummaryType SummaryType)
handlesKnownError funcLike s bb -- See Note [Known Error Conditions]
  | Just rv <- blockReturn brs bb
  , Just _ <- singlePredecessor cfg bb
  , Just _ <- retValToConstantInt rv = do
    let termInst = basicBlockTerminatorInstruction bb
        cdeps = controlDependencies cdg termInst
    foldM (checkForKnownErrorReturn funcLike bb) (Left s) cdeps
  | otherwise = return $! Left s
  where
    brs = getBlockReturns funcLike
    cdg = getCDG funcLike
    cfg = getCFG funcLike

-- FIXME: Right now there is a single-predecessor restriction.  We could
-- lift this restriction IF we do the check for ALL predecessors and if all
-- agree that this is an error.  This is still simple to state.

-- | For a given conditional branch (which is a control dependency of
-- a block returning the constant @iv@), determine whether or not the
-- condition is checking the return value of a function we know returns
-- error codes.  If it is, construct the formula that determines whether or
-- not we are on an error handling branch.
--
-- If we are, update the summary with this return value (@iv@) and any
-- error-reporting actions we see in this block.  TODO: We might be able to
-- make an argument that we should look back up multiple blocks from here
-- to the conditional check....
--
-- Note that we take the first (nearest) checked error we find.
checkForKnownErrorReturn :: (HasFunction funcLike, HasCFG funcLike,
                             HasCDG funcLike, HasBlockReturns funcLike)
                         => funcLike
                         -> BasicBlock
                         -- ^ The block returning the Int value
                         -> Either SummaryType SummaryType
                         -> Instruction
                         -> Analysis (Either SummaryType SummaryType)
checkForKnownErrorReturn _ _ acc@(Right _) _ = return acc
checkForKnownErrorReturn funcLike bb (Left s) brInst = do
  res <- runMaybeT $ do
    (target, isErrHandlingFormula) <- targetOfErrorCheckBy s brInst
    let ifacts = relevantInducedFacts funcLike bb target
        formula (x :: SInt32) = isErrHandlingFormula x &&& bAll ($x) ifacts
    case not (null ifacts) && isSat formula of
      -- This block is not handling an error
      False -> fail "Not handling an error"
      -- This block is handling an error and returning a constant, so figure
      -- out what error handling actions it is taking and modify the summary.
      True -> do
        errDesc <- branchToErrorDescriptor funcLike bb
        let w1 = Witness target "check error return"
            w2 = Witness brInst "return error code"
            d = errDesc { errorWitnesses = [w1, w2] }
        return d
  case res of
    Nothing -> return (Left s)
    Just d -> do
      fitsSuccessModel <- checkFitsSuccessModelFor f d
      case fitsSuccessModel of
        False -> do
          learnErrorCodes d
          learnErrorActions d
          liftM Right $ addErrorDescriptor f s d
        True -> liftM Left $ removeImprobableErrors f s d
  where
    f = getFunction funcLike

removeImprobableErrors :: Function -> SummaryType -> ErrorDescriptor
                       -> Analysis SummaryType
removeImprobableErrors f s (ErrorDescriptor _ (ReturnConstantInt dis) _) =
  return $ HM.adjust (S.foldr go mempty) f s
  where
    go d@(ErrorDescriptor acts (ReturnConstantInt is) ws) acc
      | S.null (S.intersection is dis) = S.insert d acc -- no overlap
      | is == dis = acc -- identical, just remove
      | otherwise = -- Some overlap, need to remove offending codes
        let consts' = S.difference is dis
            desc = ErrorDescriptor acts (ReturnConstantInt consts') ws
        in S.insert desc acc
    go d acc = S.insert d acc
removeImprobableErrors _ s _ = return s

-- | Only learn new error actions if the descriptor only includes a single
-- error action
learnErrorActions :: ErrorDescriptor -> Analysis ()
learnErrorActions (ErrorDescriptor acts (ReturnConstantInt _) _)
  | S.size acts /= 1 = return ()
  | otherwise = do
    st <- analysisGet
    case F.find isFuncallAct acts of
      Just (FunctionCall fname _) ->
        analysisPut st { errorFunctions = S.insert fname (errorFunctions st) }
      _ -> return ()
learnErrorActions _ = return ()

-- | Union in new error codes.  Note, call this carefully for now because
-- it does not filter out success codes.
learnErrorCodes :: ErrorDescriptor -> Analysis ()
learnErrorCodes (ErrorDescriptor _ (ReturnConstantInt is) _) = do
  st <- analysisGet
  analysisPut st { errorCodes = errorCodes st `S.union` is }
learnErrorCodes _ = return ()

checkFitsSuccessModelFor :: Function -> ErrorDescriptor -> Analysis Bool
checkFitsSuccessModelFor f (ErrorDescriptor _ (ReturnConstantInt is) _) = do
  st <- analysisGet
  case HM.lookup f (successModel st) of
    Nothing -> return False
    Just m -> return $ not $ S.null (is `S.intersection` m)
checkFitsSuccessModelFor _ _ = return False

-- | Given a branch instruction, if the branch is checking the return value of
-- a function call, return the function call instruction and a formula that
-- describes when an error is being checked.
--
-- FIXME: This could handle switches based on return values
targetOfErrorCheckBy :: SummaryType -> Instruction
                     -> MaybeT Analysis (Instruction, SInt32 -> SBool)
targetOfErrorCheckBy s i = do
  ics <- lift $ analysisEnvironment indirectCallSummary
  case i of
    BranchInst { branchCondition = (valueContent' ->
      InstructionC ICmpInst { cmpV1 = v1, cmpV2 = v2 })} -> do
        (ci, callee) <- firstCallInst [v1, v2]
        let callees = callTargets ics callee
        rvs <- errorReturnValues s callees
        let formula (x :: SInt32) = bAny (.==x) (map fromIntegral rvs)
        return (ci, formula)
    _ -> fail "Not a conditional branch"

-- | The other analyses identify error handling code.  This one instead looks
-- for code that we can prove is /not/ handling an error.  If we are on a
-- branch that we know is not handling an error AND it always returns the same
-- constant integer value (on all paths), we will treat that value as a
-- /success code/.
--
-- We can use that value to prevent strange code from calling a function that
-- returns an error and checking for the result (but doing nothing about it).
-- In those cases, the fallthrough could make it look like the function
-- "handled" the error by returning "success".
--
-- Basically, we use positive information to isolate bad behavior.
--
-- See tests/error-handling/reused-error-reporter.c for an example where this
-- is critical.
reportsSuccess :: (HasFunction funcLike, HasBlockReturns funcLike,
                   HasCFG funcLike, HasCDG funcLike)
               => funcLike
               -> SummaryType
               -> BasicBlock
               -> Analysis (Either SummaryType SummaryType)
reportsSuccess funcLike s bb
  | Just spred <- singlePredecessor cfg bb
  , Just rv <- blockReturnsSameIntOnPaths rets = do
    res <- runMaybeT $ do
      let brInst = basicBlockTerminatorInstruction spred
      (target, isErrHandlingFormula) <- targetOfErrorCheckBy s brInst
      let ifacts = relevantInducedFacts funcLike bb target
          formula (x :: SInt32) = isErrHandlingFormula x &&& bAll ($x) ifacts
      case not (null ifacts) && isSat formula of
        True -> fail "Not a success branch"
        -- In this block, some call that can return errors did /not/ return an
        -- error.  We also know that the value @rv@ is /always/ returned from
        -- this point, so we will conclude that @rv@ is a success code.
        False -> do
          st <- lift analysisGet
          let model = successModel st
              model' = HM.insertWith S.union f (S.singleton rv) model
          lift $ analysisPut st { successModel = model' }
          return s
    return $ maybe (Left s) Right res
  | otherwise = return (Left s)
  where
    f = getFunction funcLike
    brs = getBlockReturns funcLike
    cfg = getCFG funcLike
    rets = blockReturns brs bb

blockReturnsSameIntOnPaths :: [Value] -> Maybe Int
blockReturnsSameIntOnPaths [] = Nothing
blockReturnsSameIntOnPaths (v:vs)
  | all (==v) vs = retValToConstantInt v
  | otherwise = Nothing

-- | Return the first call instruction and its callee
firstCallInst :: [Value] -> MaybeT Analysis (Instruction, Value)
firstCallInst [] = fail "No call inst"
firstCallInst (v:vs) =
  case fromValue (ignoreCasts v) of
    Nothing -> firstCallInst vs
    Just i@CallInst { callFunction = callee } -> return (i, callee)
    _ -> firstCallInst vs


-- | Produce a formula representing all of the facts we must hold up
-- to this point.  The argument of the formula is the variable
-- representing the return value of the function we are interested in
-- (and is one of the two values passed in).
--
-- This is necessary to correctly handle conditions that are checked
-- in multiple parts (or just compound conditions).  Note that the
-- approach here is not quite complete - if part of a compound
-- condition is checked far away and we can't prove that it still
-- holds, we will miss it.  It should cover the realistic cases,
-- though.
--
-- As an example, consider:
--
-- > bytesRead = read(...);
-- > if(bytesRead < 0) {
-- >   signalError(...);
-- >   return ERROR;
-- > }
-- >
-- > if(bytesRead == 0) {
-- >   return EOF;
-- > }
-- >
-- > return OK;
--
-- Checking the first clause in isolation correctly identifies
-- signalError as an error function and ERROR as an error return code.
-- However, checking the second in isolation implies that OK is an
-- error code.
--
-- The correct thing to do is to check the second condition with the
-- fact @bytesRead >= 0@ in scope, which gives the compound predicate
--
-- > bytesRead >= 0 &&& bytesRead /= 0 &&& bytesRead == -1
--
-- or
--
-- > bytesRead >= 0 &&& bytesRead == 0 &&& bytesRead == -1
--
-- Both of these are unsat, which is what we want (since the second
-- condition isn't checking an error).
relevantInducedFacts :: (HasFunction funcLike, HasBlockReturns funcLike,
                         HasCFG funcLike, HasCDG funcLike)
                     => funcLike
                     -> BasicBlock
                     -> Instruction
                     -> [SInt32 -> SBool]
relevantInducedFacts funcLike bb0 target =
  buildRelevantFacts bb0 []
  where
    cfg = getCFG funcLike
    cdg = getCDG funcLike
    ti = basicBlockTerminatorInstruction bb0
    -- These are all conditional branch instructions
    cdeps = S.fromList $ controlDependencies cdg ti
    -- | Given that we are currently at @bb@, figure out how we got
    -- here (and what condition must hold for that to be the case).
    -- Do this by walking back in the CFG along unconditional edges
    -- and stopping when we hit a block terminated by a branch in
    -- @cdeps@ (a control-dependent branch).
    --
    -- If we ever reach a point where we have two predecessors, give
    -- up since we don't know any more facts for sure.
    buildRelevantFacts bb acc
      | S.null cdeps = acc
      | otherwise = fromMaybe acc $ do
        singlePred <- singlePredecessor cfg bb
        let br = basicBlockTerminatorInstruction singlePred
        case br of
          UnconditionalBranchInst {} ->
            return $ buildRelevantFacts singlePred acc
          bi@BranchInst { branchTrueTarget = tt
                        , branchCondition = (valueContent' ->
            InstructionC ICmpInst { cmpPredicate = p
                                  , cmpV1 = val1
                                  , cmpV2 = val2
                                  })}
            | not (S.member bi cdeps) -> Nothing
            | ignoreCasts val1 == toValue target ||
              ignoreCasts val2 == toValue target ->
              let doNeg = if bb == tt then id else bnot
                  fact' = augmentFact acc val1 val2 p doNeg
              in return $ buildRelevantFacts singlePred fact'
            | otherwise -> return $ buildRelevantFacts singlePred acc
          _ -> Nothing

augmentFact :: [SInt32 -> SBool] -> Value -> Value -> CmpPredicate
            -> (SBool -> SBool) -> [SInt32 -> SBool]
augmentFact facts val1 val2 p doNeg = fromMaybe facts $ do
  rel <- cmpPredicateToRelation p
  case (valueContent' val1, valueContent' val2) of
    (ConstantC ConstantInt { constantIntValue = (fromIntegral -> iv) }, _) ->
      return $ (\(x :: SInt32) -> doNeg (iv `rel` x)) : facts
    (_, ConstantC ConstantInt { constantIntValue = (fromIntegral -> iv)}) ->
      return $ (\(x :: SInt32) -> doNeg (x `rel` iv)) : facts
    _ -> return facts


cmpPredicateToRelation :: CmpPredicate -> Maybe (SInt32 -> SInt32 -> SBool)
cmpPredicateToRelation p =
  case p of
    ICmpEq -> return (.==)
    ICmpNe -> return (./=)
    ICmpUgt -> return (.>)
    ICmpUge -> return (.>=)
    ICmpUlt -> return (.<)
    ICmpUle -> return (.<=)
    ICmpSgt -> return (.>)
    ICmpSge -> return (.>=)
    ICmpSlt -> return (.<)
    ICmpSle -> return (.<=)
    _ -> fail "cmpPredicateToRelation is a floating point comparison"

isSat :: (SInt32 -> SBool) -> Bool
isSat f = unsafePerformIO $ do
  Just sr <- isSatisfiable Nothing f
  return sr

errorReturnValues :: SummaryType -> [Value] -> MaybeT Analysis [Int]
errorReturnValues _ [] = fail "No call targets"
errorReturnValues s [callee] = do
  fsumm <- lift $ lookupFunctionSummaryList (ErrorSummary s mempty) callee
  liftMaybe $ errRetVals fsumm
errorReturnValues s (callee:rest) = do
  fsumm <- lift $ lookupFunctionSummaryList (ErrorSummary s mempty) callee
  rvs <- liftMaybe $ errRetVals fsumm
  -- This lets us emit a warning if some callees return errors while
  -- others do not
  mapM_ (checkOtherErrorReturns rvs) rest
  return rvs
  where
    checkOtherErrorReturns rvs c = do
      fsumm <- lift $ lookupFunctionSummaryList (ErrorSummary s mempty) c
      rvs' <- liftMaybe $ errRetVals fsumm
      let inter = S.intersection (S.fromList rvs') (S.fromList rvs)
      when (S.null inter) $ emitWarning Nothing "ErrorAnalysis" ("Mismatched error return codes for indirect call " ++ show (valueName callee))

errRetVals :: [FuncAnnotation] -> Maybe [Int]
errRetVals [] = Nothing
errRetVals (FAReportsErrors _ ract : _) = do
  case ract of
    ReturnConstantInt is ->
      case F.toList is of
        [] -> Nothing
        lis -> return lis
    ReturnConstantPtr is ->
      case F.toList is of
        [] -> Nothing
        lis -> return lis
errRetVals (_:rest) = errRetVals rest

callTargets :: IndirectCallSummary -> Value -> [Value]
callTargets ics callee =
  case valueContent' callee of
    FunctionC _ -> [callee]
    ExternalFunctionC _ -> [callee]
    _ -> indirectCallInitializers ics callee

isErrRetAnnot :: FuncAnnotation -> Bool
isErrRetAnnot (FAReportsErrors _ _) = True
isErrRetAnnot _ = False

branchToErrorDescriptor :: (HasFunction funcLike, HasBlockReturns funcLike,
                            HasCFG funcLike, HasCDG funcLike)
                        => funcLike -> BasicBlock
                        -> MaybeT Analysis ErrorDescriptor
branchToErrorDescriptor funcLike bb = do
  singleRetVal <- liftMaybe $ blockReturn brs bb
  constantRc <- liftMaybe $ retValToConstantInt singleRetVal
  let rcon = if functionReturnsPointer f
             then ReturnConstantPtr
             else ReturnConstantInt
      ract = rcon (S.singleton constantRc)
      (acts, _) = foldr instToAction ([], mempty) (basicBlockInstructions bb)
  return $! ErrorDescriptor (S.fromList acts) ract []
  where
    f = getFunction funcLike
    brs = getBlockReturns funcLike

retValToConstantInt :: Value -> Maybe Int
retValToConstantInt v = do
  ConstantInt { constantIntValue = (fromIntegral -> iv) } <- fromValue v
  return iv

functionReturnsPointer :: Function -> Bool
functionReturnsPointer f =
  case functionReturnType f of
    TypePointer _ _ -> True
    _ -> False

instToAction ::Instruction -> ([ErrorAction], Set Value) -> ([ErrorAction], Set Value)
instToAction i a@(acc, ignore) =
  case i of
    CallInst { callFunction = (valueContent' -> FunctionC f)
             , callArguments = (map fst -> args)
             }
      | toValue i `S.member` ignore ->
        (acc, foldr S.insert ignore args)
      | otherwise ->
        let fname = identifierAsString (functionName f)
            argActs = foldr callArgActions mempty (zip [0..] args)
        in (FunctionCall fname argActs : acc, foldr S.insert ignore args)
    _ -> a

callArgActions :: (Int, Value)
                  -> IntMap ErrorActionArgument
                  -> IntMap ErrorActionArgument
callArgActions (ix, v) acc =
  case valueContent' v of
    ArgumentC a ->
      let atype = show (argumentType a)
          aix = argumentIndex a
      in IM.insert ix (ErrorArgument atype aix) acc
    ConstantC ConstantInt { constantIntValue = (fromIntegral -> iv) } ->
      IM.insert ix (ErrorInt iv) acc
    _ -> acc

singlePredecessor :: CFG -> BasicBlock -> Maybe BasicBlock
singlePredecessor cfg bb =
  case basicBlockPredecessors cfg bb of
    [singlePred] -> return singlePred
    _ -> Nothing

isFuncallAct :: ErrorAction -> Bool
isFuncallAct a =
  case a of
    FunctionCall _ _ -> True
    _ -> False

isErrorFuncCall :: Set String -> ErrorAction -> Bool
isErrorFuncCall funcSet errAct =
  case errAct of
    FunctionCall s _ -> S.member s funcSet
    _ -> False

liftMaybe :: Maybe a -> MaybeT Analysis a
liftMaybe = maybe mzero return

ignoreCasts :: Value -> Value
ignoreCasts v =
  case valueContent v of
    InstructionC BitcastInst { castedValue = cv } -> ignoreCasts cv
    InstructionC TruncInst { castedValue = cv } -> ignoreCasts cv
    InstructionC ZExtInst { castedValue = cv } -> ignoreCasts cv
    InstructionC SExtInst { castedValue = cv } -> ignoreCasts cv
    InstructionC IntToPtrInst { castedValue = cv } -> ignoreCasts cv
    GlobalAliasC GlobalAlias { globalAliasTarget = t } -> ignoreCasts t
    ConstantC ConstantValue { constantInstruction = BitcastInst { castedValue = cv } } -> ignoreCasts cv
    _ -> valueContent v

{- Note [Known Error Conditions]

We look for code handling known error conditions starting from basic blocks
that return a constant int value (condition 1 and 3).  Furthermore, the block
must have only a single predecessor in the CFG.  If it does not, we cannot know
which branch control flow came from and thus we don't know which conditions
*must* hold at the beginning of this block.  If we don't know the active
conditions, then we can't tell if an error is really being checked for or not
(and we'll probably just be checking a tautology for satisfiability, which
isn't useful).

In theory I believe this could make us miss error handling paths where some
optimization pass combines a few identical blocks.  However, that should
probably not be especially common.  It is better to miss some error codes than
to incorrectly report suprious error codes.

-}

{- Note [Transitive Returns with Conditions]

This note affects transitive error returns:

> rc = errorReturningFunction();
> ...
> return rc;

In the most basic scenario (if there are no conditions affecting the
return), the transitive return case is simple: the caller just returns
all of the same return codes as the callee.

If the return statement is guarded by conditions, though, this is not
so simple:

> rc = errorReturningFunction();
> if(rc == WARN) return FATAL;
> return rc;

Here, the function hosting this code cannot (at this call site) return
WARN as an error code because that is intercepted earlier and
converted to FATAL.  Thus, passing all of the return codes of
errorReturningFunction() to the caller is too much of an
overapproximation, and an avoidable one.

To deal with this, we check EACH return code from
errorReturningFunction() against the conditions in scope at this
return statement.  Assume the callee can return WARN and FATAL.

 * rc == FATAL && rc /= WARN

   This is satisfiable (assuming FATAL and WARN have different integer
   values, which they would in any real setting).  Thus, this caller can
   return FATAL.

 * rc == WARN && rc /= WARN

   This is unsatisfiable no matter how you look at it, so this return
   statement *cannot* return WARN.

The function 'addUncaughtErrors' is in charge of generating the
relevant formulas (based on the results of the general function that
collects all of the "in scope" conditions).

See test case error-handling/filters-error-codes-with-branch.c for a
full example of this issue.

The special handling of the @null priors@ case is not really necessary,
but it saves a potentially large number of pointless theorem prover calls.

-}
