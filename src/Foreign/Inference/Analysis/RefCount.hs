{-# LANGUAGE TemplateHaskell, RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns, DeriveGeneric, FlexibleContexts #-}
-- | This analysis identifies the addRef and decRef functions for a library,
-- along with the set of types that is reference counted.  This analysis is
-- unsound and incomplete, but still useful.
--
-- It first identifies the decRef function with a heuristic:
--
--  1) Find a function that conditionally calls a finalizer
--
--  2) The finalizer call is guarded by a conditional check of an
--     access path p (whose *base* is reachable from an argument to the
--     function), and
--
--  3) That same access path p is decremented
--
-- The incRef function is simply the function that increments access
-- path p
--
-- The set of types that are reference counted by a given
-- incRef/decRef pair are those types that are structural subtypes of
-- the argument to decRef (after derefencing the pointer, since all of
-- these types are passed by pointer).
module Foreign.Inference.Analysis.RefCount (
  RefCountSummary,
  identifyRefCounting,
  -- * Testing
  refCountSummaryToTestFormat
  ) where

import GHC.Generics ( Generic )

import Control.Arrow
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Getter, Lens', makeLenses, view, to, (%~), (^.), (.~) )
import Data.Foldable ( find )
import Data.HashSet ( HashSet )
import qualified Data.HashSet as HS
import Data.HashMap.Strict ( HashMap )
import qualified Data.HashMap.Strict as HM
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( catMaybes, mapMaybe )
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.ScalarEffects
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

-- import Text.Printf
-- import Debug.Trace
-- debug = flip trace

-- | The data needed to track unref functions.  The
-- @unrefCountAccessPath@ is the access path to the struct field that
-- serves as the reference count (and is decremented in the unref
-- function).
--
-- The @unrefFuncPtrCalls@ are the access paths of function pointers
-- called in the unref function.  The idea is that these functions
-- will tell us the types that are involved in reference counting for
-- object systems like glib.  For example, assuming the following line
-- is in an unref function
--
-- > obj->finalize(obj)
--
-- and (in some other function)
--
-- > obj->class = cls;
-- > cls->finalize = finalizeFoo;
--
-- and
--
-- > void finalizeFoo(Object *o) {
-- >   RealObject* obj = (RealObject*)o;
-- >   // use obj
-- > }
--
-- This tells us that the type RealObject is reference counted.  We
-- just need to look at places where the field recorded here is
-- initialized with a function and then analyze the types used by that
-- function.
data UnrefData =
  UnrefData { unrefCountAccessPath :: AbstractAccessPath
            , unrefFuncPtrCalls :: [AbstractAccessPath]
            , unrefWitnesses :: [Witness]
            }
  deriving (Eq, Generic)

instance NFData UnrefData where
  rnf = genericRnf

-- | Summary information for the reference counting analysis
data RefCountSummary =
  RefCountSummary { _conditionalFinalizers :: HashSet Define
                  , _unrefArguments :: HashMap Argument UnrefData
                  , _refArguments :: HashMap Argument (AbstractAccessPath, [Witness])
                  , _refCountedTypes :: HashMap (String, String) (HashSet Type)
                  , _refCountDiagnostics :: !Diagnostics
                  }
  deriving (Generic)

$(makeLenses ''RefCountSummary)

instance Semigroup RefCountSummary where
  (<>) = mappend

instance Monoid RefCountSummary where
  mempty = RefCountSummary mempty mempty mempty mempty mempty
  mappend (RefCountSummary s1 a1 r1 rcts1 d1) (RefCountSummary s2 a2 r2 rcts2 d2) =
    RefCountSummary { _conditionalFinalizers = s1 `mappend` s2
                    , _unrefArguments = a1 `mappend` a2
                    , _refArguments = r1 `mappend` r2
                    , _refCountedTypes = HM.unionWith HS.union rcts1 rcts2
                    , _refCountDiagnostics = d1 `mappend` d2
                    }

instance NFData RefCountSummary where
  rnf = genericRnf

instance Eq RefCountSummary where
  (RefCountSummary s1 a1 r1 rcts1 _) == (RefCountSummary s2 a2 r2 rcts2 _) =
    s1 == s2 && a1 == a2 && r1 == r2 && rcts1 == rcts2

instance HasDiagnostics RefCountSummary where
  diagnosticLens = refCountDiagnostics

-- | The summarizing functions match incref and decref functions.  We
-- need to do that here rather than on the fly since either could be
-- analyzed before the other, so every analysis step would have to try
-- to match up any outstanding references.  Here we can just do it on
-- demand.
--
-- Matching is done based on argument type and the access path used to
-- modify the reference count parameter.  If an unref function matches
-- up with exactly one ref function, they are paired by name.  The
-- code generator should deal with it appropriately.
instance SummarizeModule RefCountSummary where
  summarizeFunction _ _ = []
  summarizeArgument a (RefCountSummary _ unrefArgs refArgs _ _) =
    case HM.lookup a unrefArgs of
      Nothing ->
        case HM.lookup a refArgs of
          Nothing -> []
          Just (fieldPath, ws) ->
            case matchingTypeAndPath (argType a) fieldPath unrefCountAccessPath unrefArgs of
              Nothing -> [(PAAddRef "", ws)]
              Just fname -> [(PAAddRef fname, ws)]
      Just (UnrefData fieldPath fptrPaths ws) ->
        case matchingTypeAndPath (argType a) fieldPath fst refArgs of
          Nothing -> [(PAUnref "" (mapMaybe externalizeAccessPath fptrPaths) [], ws)]
          Just fname ->
            let unrefFunc = argDefine a
                unrefName = (\(Symbol str) -> str) (defName unrefFunc)
                ssts = HS.toList $ argumentCastedTypes a
                structuralSupertypes = mapMaybe (structTypeToName . stripPointerTypes) ssts
            in [(PAUnref fname (mapMaybe externalizeAccessPath fptrPaths) structuralSupertypes, ws)]
  summarizeType t (RefCountSummary _ _ _ rcTypes _) =
    case t of
      CStruct n _ ->
        case find entryForType (HM.toList rcTypes) of
          Nothing -> []
          Just ((addRef, decRef), _) -> [(TARefCounted addRef decRef, [])]
        where
          entryForType (_, typeSet) =
            let groupTypeNames = mapMaybe (structTypeToName . stripPointerTypes) (HS.toList typeSet)
            in n `elem` groupTypeNames
      _ -> []

matchingTypeAndPath :: Type
                       -> AbstractAccessPath
                       -> (a -> AbstractAccessPath)
                       -> HashMap Argument a
                       -> Maybe String
matchingTypeAndPath t accPath toPath m =
  case filter matchingPair pairs of
    [(singleMatch, _)] ->
      let f = argDefine singleMatch
      in Just $ (\(Symbol str) -> str) (defName f)
    _ -> Nothing
  where
    pairs = HM.toList m
    matchingPair (arg, d) = argType arg == t && (toPath d) == accPath

type Analysis = AnalysisMonad () ()

-- | The main analysis to identify both incref and decref functions.
identifyRefCounting :: forall compositeSummary funcLike . (FuncLike funcLike, HasDefine funcLike, HasCFG funcLike)
                       => DependencySummary
                       -> Lens' compositeSummary RefCountSummary
                       -> Getter compositeSummary FinalizerSummary
                       -> Getter compositeSummary ScalarEffectSummary
                       -> ComposableAnalysis compositeSummary funcLike
identifyRefCounting ds lns depLens1 depLens2 =
  composableDependencyAnalysisM runner refCountAnalysis lns depLens
  where
    runner a = runAnalysis a ds () ()
    depLens :: Getter compositeSummary (FinalizerSummary, ScalarEffectSummary)
    depLens = to (view depLens1 &&& view depLens2)

-- | Check to see if the given function is a conditional finalizer.
-- If it is, return the call instruction that (conditionally) invokes
-- a finalizer AND the argument being finalized.
--
-- This argument is needed for later steps.
--
-- Note that no finalizer is allowed to be a conditional finalizer
isConditionalFinalizer :: FinalizerSummary
                          -> Define
                          -> Analysis (Maybe (Stmt, Argument))
isConditionalFinalizer summ f = do
  fin <- functionIsFinalizer summ f
  case fin of
    True -> return Nothing
    False -> do
      -- Find the list of all arguments that are finalized in the
      -- function.
      finArgs <- mapM (isFinalizerCall summ) (defStmts f)
      case catMaybes finArgs of
--      case mapMaybe (isFinalizerCall summ) (defStmts f) of
        [] -> return Nothing
        -- If there is more than one match, ensure that they all
        -- finalize the same argument.  If that is not the case,
        -- return Nothing
        x@(_, a) : rest ->
          case all (==a) (map snd rest) of
            False -> return Nothing
            True -> return (Just x)

isFinalizerCall :: FinalizerSummary
                   -> Stmt
                   -> Analysis (Maybe (Stmt, Argument))
isFinalizerCall summ i =
  case stmtInstr i of
    Call _ _ callee args -> callFinalizes summ i callee args
    Invoke _ callee args _ _ -> callFinalizes summ i callee args
    _ -> return Nothing

-- | If the given call (value + args) is a finalizer, return the
-- Argument it is finalizing.  If it is a finalizer but does not
-- finalize an argument, returns Nothing.
callFinalizes :: FinalizerSummary
                 -> Stmt
                 -> Value -- ^ The called value
                 -> [Value] -- ^ Actual arguments
                 -> Analysis (Maybe (Stmt, Argument))
callFinalizes fs i callee args = do
  finArgs <- mapM isFinalizedArgument (zip [0..] args)
  case catMaybes finArgs of
    [finArg] -> return $ Just (i, finArg)
    _ -> return Nothing
  where
    isFinalizedArgument (ix, arg) = do
      annots <- lookupArgumentSummaryList fs callee ix
      case (PAFinalize `elem` annots, valValue (valueContent' arg)) of
        (False, _) -> return Nothing
        -- We only return a hit if this is an Argument to the *caller*
        -- that is being finalized
        (True, ValIdent (IdentValArgument a)) -> return (Just a)
        (True, _) -> return Nothing

functionIsFinalizer :: FinalizerSummary -> Define -> Analysis Bool
functionIsFinalizer fs f = do
  allArgAnnots <- mapM (lookupArgumentSummaryList fs f) [0..maxArg]
  return $ any argFinalizes allArgAnnots
  where
    maxArg = length (defArgs f) - 1
    argFinalizes annots = PAFinalize `elem` annots

refCountAnalysis :: (FuncLike funcLike, HasCFG funcLike, HasDefine funcLike)
                    => (FinalizerSummary, ScalarEffectSummary)
                    -> funcLike
                    -> RefCountSummary
                    -> Analysis RefCountSummary
refCountAnalysis (finSumm, seSumm) funcLike summ = do
  let summ' = incRefAnalysis seSumm f summ
  condFinData <- isConditionalFinalizer finSumm f
  rcTypes <- refCountTypes f

  let summ'' = (refCountedTypes %~ HM.unionWith HS.union rcTypes) summ'

  case condFinData of
    Nothing -> return summ''
    Just (cfi, cfa) ->
      let summWithCondFin = (conditionalFinalizers %~ HS.insert f) summ''
          finWitness = Witness cfi "condfin"
          fptrAccessPaths = mapMaybe (indirectCallAccessPath cfa) (defStmts f)
          -- If this is a conditional finalizer, figure out which
          -- field (if any) is unrefed.
          newUnref = case (decRefCountFields seSumm f, defArgs f) of
            ([(accPath, decWitness)], [a]) ->
              let ud = UnrefData accPath fptrAccessPaths [finWitness, decWitness]
              in HM.insert a ud
            _ -> id
          summWithUnref = (unrefArguments %~ newUnref) summWithCondFin
      in return summWithUnref
  where
    f = getDefine funcLike

refCountTypes :: Define -> Analysis (HashMap (String, String) (HashSet Type))
refCountTypes f = do
  ds <- getDependencySummary
  let fptrFuncs = mapMaybe (identifyIndicatorFields ds) (defStmts f)
      rcTypesByField = map (second unaryFuncToCastedArgTypes) fptrFuncs
      structuralRefTypes = mapMaybe (subtypeRefCountTypes ds) interfaceTypes
      rcTypes = rcTypesByField ++ structuralRefTypes
  return $ foldr (\(k, v) m -> HM.insertWith HS.union k v m) mempty rcTypes
  where
    interfaceTypes = defRetType f : map argType (defArgs f)
    identifyIndicatorFields ds i =
      case stmtInstr i of
        Store (valValue . valueContent' -> ValSymbol (SymValDefine sv)) _ _ _ ->
          case accessPath i of
            Nothing -> Nothing
            Just cAccPath -> do
              let aAccPath = abstractAccessPath cAccPath
              refFuncs <- refCountFunctionsForField ds aAccPath
              return (refFuncs, sv)
        _ -> Nothing

subtypeRefCountTypes :: DependencySummary
                        -> Type
                        -> Maybe ((String, String), HashSet Type)
subtypeRefCountTypes ds t0 = go t1
  where
    t1 = stripPointerTypes t0
    go t = case t of
      Struct _ (structuralParent:_) _ -> do
        -- If this type is known to be ref counted, just return.
        -- Otherwise, check if any structural parents of this type are
        -- known to be ref counted.  We check this by considering the
        -- constituent types of t.  If the first one is a struct type,
        -- that is the structural parent (since they are
        -- interchangable to code expecting the parent type).
        case isRefCountedObject ds t of
          Just rcFuncs -> return (rcFuncs, HS.singleton t1)
          Nothing -> go structuralParent
      Struct _ _ _ -> do
        rcFuncs <- isRefCountedObject ds t
        return (rcFuncs, HS.singleton t1)
      _ -> Nothing


-- | If the function is unary, return a set with the type of that
-- argument along with all of the types it is casted to in the body of
-- the function
unaryFuncToCastedArgTypes :: Define -> HashSet Type
unaryFuncToCastedArgTypes f =
  case defArgs f of
    [p] -> argumentCastedTypes p
    _ -> mempty

argumentCastedTypes :: Argument -> HashSet Type
argumentCastedTypes a =
  fst $ foldr captureCastedType s0 (defStmts f)
  where
    f = argDefine a
    s0 = (HS.singleton (argType a), HS.singleton (toValue a))

    captureCastedType i acc@(ts, vs) =
      case stmtInstr i of
        Conv BitCast cv _ ->
          case cv `HS.member` vs of
            False -> acc
            True -> (HS.insert (valType (toValue i)) ts, HS.insert (toValue i) vs)
        _ -> acc


incRefAnalysis :: ScalarEffectSummary -> Define -> RefCountSummary -> RefCountSummary
incRefAnalysis seSumm f summ =
  case (incRefCountFields seSumm f, defArgs f) of
    ([], _) -> summ
    ([(fieldPath, w)], [a]) ->
      let newAddRef = HM.insert a (fieldPath, [w]) (summ ^. refArguments)
      in (refArguments .~ newAddRef) summ
    _ -> summ

-- Note, here pass in the argument that is conditionally finalized.  It should
-- be an argument to this indirect call.  Additionally, the base of the access
-- path should be this argument

-- | If the instruction is an indirect function call, return the
-- *concrete* AccessPath from which the function pointer was obtained.
indirectCallAccessPath :: Argument -> Stmt -> Maybe AbstractAccessPath
indirectCallAccessPath arg i =
  case stmtInstr i of
    Call _ _ f actuals -> notDirect f actuals
    Invoke _ f actuals _ _ -> notDirect f actuals
    _ -> Nothing
  where
    -- The only indirect calls occur through a load instruction.
    -- Additionally, we want the Argument input to the caller to
    -- appear in the argument list of the indirect call.
    --
    -- Ideally, we would like to ensure that the function pointer
    -- being invoked is in some way derived from the argument being
    -- finalized.  This is a kind of backwards reachability from the
    -- base of the access path
    notDirect v actuals =
      case (any (isSameArg arg) actuals, valValue (valueContent' v)) of
        (True, ValIdent (IdentValStmt callee@(stmtInstr -> Load {}))) -> do
          accPath <- accessPath callee
          return $! abstractAccessPath accPath
        _ -> Nothing

isSameArg :: Argument -> Value -> Bool
isSameArg arg v =
  case valValue (valueContent' v) of
    ValIdent (IdentValArgument a) -> arg == a
    _ -> False

-- FIXME: Equality with arg isn't enough because of bitcasts

-- | Find all of the fields of argument objects that are decremented
-- in the given Function, returning the affected AbstractAccessPaths
decRefCountFields :: ScalarEffectSummary -> Define -> [(AbstractAccessPath, Witness)]
decRefCountFields seSumm f = mapMaybe (checkDecRefCount seSumm) allInsts
  where
    allInsts = concatMap bbStmts (defBody f)

-- | Likewise, but for incremented fields
incRefCountFields :: ScalarEffectSummary -> Define -> [(AbstractAccessPath, Witness)]
incRefCountFields seSumm f = mapMaybe (checkIncRefCount seSumm) allInsts
  where
    allInsts = concatMap bbStmts (defBody f)

-- | This function checks whether or not the given 'Instruction'
-- decrements a reference count (really, any integer field embedded in
-- an object).  If it does, the function returns the
-- AbstractAccessPath that was decremented.
--
-- FIXME: Add support for cmpxchg?
checkDecRefCount :: ScalarEffectSummary
                    -> Stmt
                    -> Maybe (AbstractAccessPath, Witness)
checkDecRefCount seSumm i = do
  p <- case stmtInstr i of
    AtomicRW _ AtomicSub _ (valValue -> ValInteger 1) _ _ ->
      absPathIfArg i
    AtomicRW _ AtomicAdd _ (valValue -> ValInteger (-1)) _ _ ->
      absPathIfArg i
    Store _ (valueContent' -> ValInstr (Arith Sub {}
        (valValue . valueContent' -> ValIdent (IdentValStmt oldRefCount))
        (valValue . valueContent' -> ValInteger 1))) _ _ ->
      absPathIfArg oldRefCount
    Store _ (valueContent' -> ValInstr (Arith Add {}
        (valValue . valueContent' -> ValIdent (IdentValStmt oldRefCount))
        (valValue . valueContent' -> ValInteger (-1)))) _ _ ->
      absPathIfArg oldRefCount
    Store _ (valueContent' -> ValInstr (Arith Add {}
        (valValue . valueContent' -> ValInteger (-1))
        (valValue . valueContent' -> ValIdent (IdentValStmt oldRefCount)))) _ _ ->
      absPathIfArg oldRefCount
    Call _ _ (valValue . valueContent' -> ValSymbol (SymValDefine f)) [a] ->
      absPathThroughCall seSumm scalarEffectSubOne (defArgs f) a
    Invoke _ (valValue . valueContent' -> ValSymbol (SymValDefine f)) [a] _ _ ->
      absPathThroughCall seSumm scalarEffectSubOne (defArgs f) a
    _ -> Nothing
  return (p, Witness i "decr")

-- | Analogous to 'checkDecRefCount', but for increments
checkIncRefCount :: ScalarEffectSummary
                    -> Stmt
                    -> Maybe (AbstractAccessPath, Witness)
checkIncRefCount seSumm i = do
  p <- case stmtInstr i of
    AtomicRW _ AtomicSub _ (valValue -> ValInteger (-1)) _ _ ->
      absPathIfArg i
    AtomicRW _ AtomicAdd _ (valValue -> ValInteger 1) _ _ ->
      absPathIfArg i
    Store _ (valueContent' -> ValInstr (Arith Sub {}
        (valValue . valueContent' -> ValIdent (IdentValStmt oldRefCount))
        (valValue . valueContent' -> ValInteger (-1)))) _ _ ->
      absPathIfArg oldRefCount
    Store _ (valueContent' -> ValInstr (Arith Add {}
        (valValue . valueContent' -> ValIdent (IdentValStmt oldRefCount))
        (valValue . valueContent' -> ValInteger 1))) _ _ ->
      absPathIfArg oldRefCount
    Store _ (valueContent' -> ValInstr (Arith Add {}
        (valValue . valueContent' -> ValInteger 1)
        (valValue . valueContent' -> ValIdent (IdentValStmt oldRefCount)))) _ _ ->
      absPathIfArg oldRefCount
    Call _ _ (valValue . valueContent' -> ValSymbol (SymValDefine f)) [a] ->
      absPathThroughCall seSumm scalarEffectSubOne (defArgs f) a
    Invoke _ (valValue . valueContent' -> ValSymbol (SymValDefine f)) [a] _ _ ->
      absPathThroughCall seSumm scalarEffectSubOne (defArgs f) a
    _ -> Nothing
  return (p, Witness i "incr")

-- | At a call site, if the callee has a scalar effect on its argument,
-- match up the access path of the actual argument passed to the callee
-- with the access path affected by the callee.
--
-- The scalar effect desired is controlled by the second argument and
-- should probably be one of
--
--  * scalarEffectAddOne
--
--  * scalarEffectSubOne
--
-- This function is meant to determine the effective abstract access
-- path of increments/decrements performed by called functions on data
-- in the caller.  For example:
--
-- > void decRef(Object * o) {
-- >   atomic_dec(&o->refCount);
-- > }
--
-- In this example, @atomic_dec@ only decrements the location passed
-- to it.  The abstract access path of the call instruction, however,
-- (and the value returned by this function) is Object/refCount.
--
-- This function deals only with single-argument callees
absPathThroughCall :: ScalarEffectSummary
                      -> (ScalarEffectSummary -> Argument -> Maybe AbstractAccessPath) -- ^ Type of access
                      -> [Argument] -- ^ Argument list of the callee
                      -> Value -- ^ Actual argument at call site
                      -> Maybe AbstractAccessPath
absPathThroughCall seSumm effect [singleFormal] actual = do
  -- This is the access path of the argument of the callee (if and
  -- only if the function subtracts one from an int component of the
  -- argument).  The access path describes *which* component of the
  -- argument is modified.
  calleeAccessPath <- effect seSumm singleFormal
  case valValue (valueContent' actual) of
    ValIdent (IdentValStmt i) -> do
      actualAccessPath <- accessPath i
      -- Now see if the actual passed to this call is derived from one
      -- of the formal parameters of the current function.  This
      -- access path tells us which component of the argument was
      -- passed to the callee.
      case valValue (valueContent' (accessPathBaseValue actualAccessPath)) of
        -- If it really was derived from an argument, connect up
        -- the access paths for the caller and callee so we have a
        -- single description of the field that was modified
        -- (interprocedurally).
        ValIdent (IdentValArgument _) ->
          abstractAccessPath actualAccessPath `appendAccessPath` calleeAccessPath
        _ -> Nothing
    _ -> Nothing
absPathThroughCall _ _ _ _ = Nothing

-- | If the Instruction produces an access path rooted at an Argument,
-- return the corresponding AbstractAccessPath
absPathIfArg :: Stmt -> Maybe AbstractAccessPath
absPathIfArg i =
  case accessPath i of
    Nothing -> Nothing
    Just cap ->
      case valValue (valueContent' (accessPathBaseValue cap)) of
        ValIdent (IdentValArgument _) -> Just (abstractAccessPath cap)
        _ -> Nothing

-- Testing

-- | Extract a map of unref functions to ref functions
refCountSummaryToTestFormat :: RefCountSummary -> Map String String
refCountSummaryToTestFormat (RefCountSummary _ unrefArgs refArgs _ _) =
  foldr addIfRefFound mempty (HM.toList unrefArgs)
  where
    addIfRefFound (uarg, UnrefData fieldPath _ _) acc =
      let ufunc = (\(Symbol str) -> str) $ defName $ argDefine uarg
      in case matchingTypeAndPath (argType uarg) fieldPath fst refArgs of
        Nothing -> acc
        Just rfunc -> M.insert ufunc rfunc acc
