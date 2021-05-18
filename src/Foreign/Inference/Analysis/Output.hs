{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns, DeriveGeneric, TemplateHaskell #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleContexts #-}
-- | This analysis identifies output parameters.
--
-- Output parameters are those pointer parameters whose target memory
-- is never read from, only written to.  This implies that the value
-- at the target of the pointer at the time of a call is irrelevant.
-- Bindings can then automatically manage these parameters for
-- callers.
--
-- It is a dataflow analysis that classifies pointer parameters as
-- input, output, or both.  The initial value for each pointer
-- parameter is unused and the meet operator is point-wise least upper
-- bound (LUB).
--
-- This analysis only deals with pointers to scalar types and pointers
-- to aggregates.  A pointer to an aggregate is an output parameter if
-- all of the fields of the aggregate are overwritten.
module Foreign.Inference.Analysis.Output (
  -- * Interface
  OutputSummary,
  identifyOutput,

  -- * Testing
  outputSummaryToTestFormat
  ) where

import GHC.Generics ( Generic )

import Control.Arrow ( second )
import Control.DeepSeq
import Control.DeepSeq.Generics ( genericRnf )
import Control.Lens ( Lens', makeLenses, (%~), (^.) )
import Control.Monad ( foldM )
import Data.List ( find, groupBy )
import Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import Data.Maybe (mapMaybe)

import LLVM.Analysis
import LLVM.Analysis.CFG
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Dataflow

import Foreign.Inference.AnalysisMonad
import Foreign.Inference.Diagnostics
import Foreign.Inference.Interface

-- | Either the finalizer for an output argument, a token indicating
-- that the output argument was a NULL pointer, or a token indicating
-- that more than one out finalizer is involved.
-- data OutFinalizer = OutFinalizer String
--                   | OutFinalizerNull
--                   | OutFinalizerConflict
--                   deriving (Eq, Ord)

data ArgumentDirection = ArgIn
                       | ArgOut
                       -- | ArgOutAlloc (Set Instruction, OutFinalizer)
                         -- ^ Instructions and their associated finalizer
                       | ArgBoth
                       deriving (Eq, Ord, Generic)

instance Show ArgumentDirection where
  show ArgIn = "in"
  show ArgOut = "out"
  show ArgBoth = "both"

instance NFData ArgumentDirection

-- | Tracks the direction of each argument
type SummaryType = Map Argument (ArgumentDirection, [Witness])
-- | Tracks the direction of fields of pointer-to-struct arguments.
-- If all of the fields of a struct argument are ArgOut, the struct
-- argument is output.
type FieldSummaryType = Map (Argument, Int) (ArgumentDirection, [Witness])
data OutputSummary =
  OutputSummary { _outputSummary :: SummaryType
                , _outputFieldSummary :: FieldSummaryType
                , _outputDiagnostics :: Diagnostics
                }
  deriving (Generic)

$(makeLenses ''OutputSummary)

data OutInfo = OI { _outputInfo :: !(Map Argument (ArgumentDirection, Set Witness))
                  , _outputFieldInfo :: !(Map (Argument, Int) (ArgumentDirection, Set Witness))
                  }
             deriving (Eq, Show)

$(makeLenses ''OutInfo)

instance Eq OutputSummary where
  (OutputSummary s1 fs1 _) == (OutputSummary s2 fs2 _) =
    s1 == s2 && fs1 == fs2

instance Semigroup OutputSummary where
  (<>) = mappend

instance Monoid OutputSummary where
  mempty = OutputSummary mempty mempty mempty
  mappend (OutputSummary s1 sf1 d1) (OutputSummary s2 sf2 d2) =
    OutputSummary (M.union s1 s2) (M.union sf1 sf2) (mappend d1 d2)

instance NFData OutputSummary where
  rnf = genericRnf

instance HasDiagnostics OutputSummary where
  diagnosticLens = outputDiagnostics

instance SummarizeModule OutputSummary where
  summarizeFunction _ _ = []
  summarizeArgument = summarizeOutArgument

summarizeOutArgument :: Argument -> OutputSummary -> [(ParamAnnotation, [Witness])]
summarizeOutArgument a (OutputSummary s sf _) =
  case M.lookup a s of
    Nothing ->
      case argumentFieldCount a of
        Nothing -> []
        Just flds ->
          let argFieldDirs = M.toList (M.filterWithKey (matchesArg a) sf)
          in case length argFieldDirs == flds && all isOutField argFieldDirs of
            False -> []
            True -> [(PAOut, combineWitnesses argFieldDirs)]

    Just (ArgIn, _) -> []
    Just (ArgOut, ws) -> [(PAOut, ws)]
    Just (ArgBoth, ws) -> [(PAInOut, ws)]

matchesArg :: Argument -> (Argument, a) -> b -> Bool
matchesArg a (ma, _) _ = ma == a

isOutField :: (a, (ArgumentDirection, b)) -> Bool
isOutField (_, (ArgOut, _)) = True
isOutField _ = False

combineWitnesses :: [(a, (b, [Witness]))] -> [Witness]
combineWitnesses = concatMap (snd . snd)


-- | If the argument is a pointer to a struct, return the number of
-- fields in the struct.  Otherwise, return Nothing.
argumentFieldCount :: Argument -> Maybe Int
argumentFieldCount a =
  case argType a of
    (PtrTo (Struct _ flds _)) -> Just (length flds)
    _ -> Nothing

data OutData = OD { moduleSummary :: OutputSummary
                  }

-- | Note that array parameters are not out parameters, so we rely on
-- the Array analysis to let us filter those parameters out of our
-- results.
identifyOutput :: forall compositeSummary funcLike . (FuncLike funcLike, HasCFG funcLike, HasDefine funcLike)
                  => Module
                  -> DependencySummary
                  -> Lens' compositeSummary OutputSummary
                  -> ComposableAnalysis compositeSummary funcLike
identifyOutput m ds lns =
  composableAnalysisM runner (outAnalysis m) lns
  where
    runner a = runAnalysis a ds constData ()
    constData = OD mempty

meetDir :: ArgumentDirection -> ArgumentDirection -> ArgumentDirection
meetDir ArgIn ArgIn = ArgIn
meetDir ArgOut ArgOut = ArgOut
meetDir ArgIn ArgOut = ArgBoth
meetDir ArgOut ArgIn = ArgBoth
meetDir ArgBoth _ = ArgBoth
meetDir _ ArgBoth = ArgBoth

top :: OutInfo
top = OI mempty mempty

meetOutInfo :: OutInfo -> OutInfo -> OutInfo
meetOutInfo (OI m1 mf1) (OI m2 mf2) =
  OI (M.unionWith meetWithWitness m1 m2) (M.unionWith meetWithWitness mf1 mf2)
  where
    meetWithWitness (v1, w1) (v2, w2) = (meetDir v1 v2, S.union w1 w2)

type Analysis = AnalysisMonad OutData ()

outAnalysis :: (FuncLike funcLike, HasDefine funcLike, HasCFG funcLike)
               => Module
               -> funcLike
               -> OutputSummary
               -> Analysis OutputSummary
outAnalysis m funcLike s = do
  let envMod e = e { moduleSummary = s
                   }
      analysis = bwdDataflowAnalysis top meetOutInfo (outTransfer m)
  funcInfo <- analysisLocal envMod (dataflow funcLike analysis top)
  let OI exitInfo fexitInfo = dataflowResult funcInfo -- (functionEntryInstruction f)
--  let OI exitInfo fexitInfo = dataflowResult funcInfo
  let exitInfo' = M.map (second S.toList) exitInfo
      fexitInfo' = M.map (second S.toList) fexitInfo
  -- Merge the local information we just computed with the global
  -- summary.  Prefer the locally computed info if there are
  -- collisions (could arise while processing SCCs).
  return $! (outputSummary %~ M.union exitInfo') $ (outputFieldSummary %~ M.union fexitInfo') s
  where
    f = getDefine funcLike

-- | If the given @callInst@ is an allocated value (i.e., call to an
-- allocator) and it does not escape via any means other than the
-- given @storeInst@ (which stored it into an 'Argument'), return the
-- name of its associated finalizer.
-- isAllocatedValue :: Instruction -> Value -> Instruction -> Analysis (Maybe String)
-- isAllocatedValue storeInst calledFunc callInst = do
--   asum <- analysisEnvironment allocatorSummary
--   esum <- analysisEnvironment escapeSummary
--   annots <- lookupFunctionSummaryList asum calledFunc
--   case mapMaybe isAllocAnnot annots of
--     [fin] ->
--       case instructionEscapesWith ignoreStore callInst esum of
--         Nothing -> return $! Just fin
--         Just _ -> return Nothing
--     _ -> return Nothing
--   where
--     ignoreStore = (== storeInst)
--     isAllocAnnot (FAAllocator fin) = Just fin
--     isAllocAnnot _ = Nothing

-- | This transfer function only needs to be concerned with Load and
-- Store instructions (for now).  Loads add in an ArgIn value. Stores
-- add an ArgOut.
--
-- Note, we don't use valueContent' to strip bitcasts here since
-- accesses to bitfields use lots of interesting bitcasts and give us
-- false positives.
outTransfer :: Module -> OutInfo -> Stmt -> Analysis OutInfo
outTransfer m info i =
  case stmtInstr i of
    Load (valValue -> ValIdent (IdentValArgument ptr)) _ _ ->
      return $! merge outputInfo i ptr ArgIn info
    Store _ (valValue -> ValIdent (IdentValArgument ptr)) _ _ ->
      return $! merge outputInfo i ptr ArgOut info
    AtomicRW _ _ (valValue -> ValIdent (IdentValArgument ptr)) _ _ _ ->
      return $! merge outputInfo i ptr ArgBoth info
    CmpXchg _ _ (valValue -> ValIdent (IdentValArgument ptr)) _ _ _ _ _ ->
      return $! merge outputInfo i ptr ArgBoth info

    Load (ValInstr
      (GEP _ (valValue -> ValIdent (IdentValArgument ptr))
          [ valValue -> ValInteger 0
          , valValue -> ValInteger fldNo
          ])) _ _ ->
      return $! merge outputFieldInfo i (ptr, fromIntegral fldNo) ArgIn info
    Store _ (ValInstr
      (GEP _ (valValue -> ValIdent (IdentValArgument ptr))
          [ valValue -> ValInteger 0
          , valValue -> ValInteger fldNo
          ])) _ _ ->
      return $! merge outputFieldInfo i (ptr, fromIntegral fldNo) ArgOut info
    AtomicRW _ _ (ValInstr
      (GEP _ (valValue -> ValIdent (IdentValArgument ptr))
          [ valValue -> ValInteger 0
          , valValue -> ValInteger fldNo
          ])) _ _ _ ->
      return $! merge outputFieldInfo i (ptr, fromIntegral fldNo) ArgBoth info
    CmpXchg _ _ (ValInstr
      (GEP _ (valValue -> ValIdent (IdentValArgument ptr))
          [ valValue -> ValInteger 0
          , valValue -> ValInteger fldNo
          ])) _ _ _ _ _ ->
      return $! merge outputFieldInfo i (ptr, fromIntegral fldNo) ArgBoth info

    Call _ _ f args -> callTransfer m info i f args
    Invoke _ f args _ _-> callTransfer m info i f args

    _ -> return info


isMemcpy :: Value -> Bool
isMemcpy v =
  case valValue (valueContent' v) of
    (ValSymbol (SymValDeclare Declare { decName = fname })) ->
      show fname == "@llvm.memcpy.p0i8.p0i8.i32" || show fname == "@llvm.memcpy.p0i8.p0i8.i64"
    _ -> False


-- | A broken out transfer function for calls.  This deals with traversing
-- the list of arguments in a reasonable way to correctly handle argument
-- aliasing.  See Note [Argument Aliasing]
callTransfer :: Module -> OutInfo -> Stmt -> Value -> [Value] -> Analysis OutInfo
callTransfer m info i f args = do
  let indexedArgs = zip [0..] args
  modSumm <- analysisEnvironment moduleSummary -- FIXME: Change this to an OutputSummary?
  case (isMemcpy f, args) of
    (True, [dest, src, bytes, _, _]) ->
      memcpyTransfer m info i dest src bytes
    _ -> do
      info' <- foldM (checkInOutArg modSumm) info indexedArgs
      info'' <- foldM (checkInArg modSumm) info' indexedArgs
      foldM (checkOutArg modSumm) info'' indexedArgs
  where
    checkInOutArg ms acc (ix, arg) =
      case valValue (valueContent' arg) of
        ValIdent (IdentValArgument a) -> do
          attrs <- lookupArgumentSummaryList ms f ix
          case PAInOut `elem` attrs of
            True -> return $! merge outputInfo i a ArgBoth acc
            False -> return acc
        _ -> return acc
    checkInArg ms acc (ix, arg) =
      case valValue (valueContent' arg) of
        ValIdent (IdentValArgument a) -> do
          attrs <- lookupArgumentSummaryList ms f ix
          case find isAnyOut attrs of
            Just _ -> return acc
            Nothing -> return $ merge outputInfo i a ArgIn acc
        _ -> return acc
    checkOutArg ms acc (ix, arg) =
      case valValue (valueContent' arg) of
        ValIdent (IdentValArgument a) -> do
          attrs <- lookupArgumentSummaryList ms f ix
          case PAOut `elem` attrs of
            True -> return $! merge outputInfo i a ArgOut acc
            False -> return $! merge outputInfo i a ArgIn acc
        _ -> return acc

isAnyOut :: ParamAnnotation -> Bool
isAnyOut PAOut = True
isAnyOut _ = False


-- TODO Move these general functions somewhere else

getTypeSizeInBits :: Module -> Type -> Maybe Int
getTypeSizeInBits m t = case t of
  (PrimType t') -> case t' of
    Label -> getPointerSizeInBits m 0
    (Integer w) -> Just $ fromIntegral w
    (FloatType Half) -> Just 16
    (FloatType Float) -> Just 32
    (FloatType Double) -> Just 64
    (FloatType X86_fp80) -> Just 80
    (FloatType Fp128) -> Just 128
    (FloatType PPC_fp128) -> Just 128
    X86mmx -> Just 64
    _ -> Nothing
  (Array w t') -> (fromIntegral w *) <$> getTypeSizeInBits m t'
  (PtrTo _) -> getPointerSizeInBits m 0 -- TODO deal with other address spaces
  (Struct _ ts _) -> sum <$> traverse (getTypeSizeInBits m) ts
  (Vector w t') -> (fromIntegral w *) <$> getTypeSizeInBits m t'
  _ -> Nothing

getPointerSizeInBits :: Module -> Int -> Maybe Int
getPointerSizeInBits m _addrspace = safeHead $ mapMaybe f $ modDataLayout m where
  safeHead [x] = Just x
  safeHead _ = Nothing

  f (PointerSize 0 s _ _) = Just s
  f _ = Nothing

moduleTypeSizes :: Module -> Type -> Maybe Int
moduleTypeSizes m = fmap (ceiling . (/ (8.0 :: Double)) . fromIntegral) . getTypeSizeInBits m

-- | A memcpy is treated as an assignment if the number of bytes copied
-- matches the size of the destination of the memcpy.  We strip bitcasts
-- when checking this because the arguments to memcpy are void*, and
-- that void types have no size.
memcpyTransfer :: Module -> OutInfo -> Stmt -> Value -> Value -> Value -> Analysis OutInfo
memcpyTransfer m info i dest src (valValue -> ValInteger byteCount)
  | PtrTo destBaseTy <- valType (stripBitcasts dest)
  , Just tySize <- moduleTypeSizes m destBaseTy
  , tySize /= fromIntegral byteCount =
    case isArgument src of
      Just sarg -> return $! merge outputInfo i sarg ArgIn info
      Nothing -> return info
  | otherwise =
    case (isArgument dest, isArgument src) of
      (Just darg, Just sarg) ->
        return $! merge outputInfo i darg ArgOut $ merge outputInfo i sarg ArgIn info
      (Just darg, Nothing) -> return $! merge outputInfo i darg ArgOut info
      (Nothing, Just sarg) -> return $! merge outputInfo i sarg ArgIn info
      _ -> return info
  where
    isArgument x = case valValue (stripBitcasts x) of
                     ValIdent (IdentValArgument a) -> Just a
                     _ -> Nothing
memcpyTransfer _ info _ _ _ _ = return info

-- | The transfer function encodes the following:
--
-- > f(*p = x, inState) = OUT
-- > f(x = *p, inState) = IN `GLB` inState
--
-- There is a shorthand where we can use INOUT for atomic ptr ops
-- since they are a read+write.  Thus, both OUT and INOUT are simple
-- cases where they just overwrite the old value.  If the new value is
-- IN, then we do a join with the old value (if any).
merge :: (Ord k)
         => Lens' info (Map k (ArgumentDirection, Set Witness)) -- ^ Param or field
         -> Stmt -- ^ Instruction causing the merge
         -> k -- ^ The base value (either a param or field owner)
         -> ArgumentDirection -- ^ New direction
         -> info -- ^ Old info
         -> info
merge lns i arg ArgBoth info =
  let ws = S.singleton (Witness i (show ArgBoth))
  in (lns %~ M.insert arg (ArgBoth, ws)) info
merge lns i arg ArgOut info =
  let ws = S.singleton (Witness i (show ArgOut))
  in (lns %~ M.insert arg (ArgOut, ws)) info
merge lns i arg ArgIn info =
  case M.lookup arg (info ^. lns) of
    -- No old value, so take the new one
    Nothing ->
      let ws = S.singleton (Witness i (show ArgIn))
      in (lns %~ M.insert arg (ArgIn, ws)) info
    Just (oldVal, ws) ->
      let newDir = ArgIn `meetDir` oldVal
          nw = Witness i (show newDir)
      in (lns %~ M.insert arg (newDir, S.insert nw ws)) info
         {-
    -- The old value was Both, so just keep it
    Just (ArgBoth, _) -> info
    -- Since the new value is not Both, we can't advance from Out with
    -- linear control flow (only at control flow join points).
    Just (ArgOut, _) -> info
    Just (ArgIn, ws) ->
      case newVal of
        ArgOut ->
          let nw = Witness i (show ArgBoth)
          in (lns %~ M.insert arg (ArgBoth, S.insert nw ws)) info
        -- ArgOutAlloc _ ->
        --   let nw = Witness i (show ArgBoth)
        --   in (lns %~ M.insert arg (ArgBoth, S.insert nw ws)) info
        ArgIn -> info
        ArgBoth -> error "Foreign.Inference.Analysis.Output.merge(2): Infeasible path"
-}

removeArrayPtr :: Argument -> OutInfo -> OutInfo
removeArrayPtr a (OI oi foi) = OI (M.delete a oi) foi

-- Testing

-- | Convert an Output summary to a format more suitable for
-- testing
outputSummaryToTestFormat :: OutputSummary -> Map String (Set (String, ParamAnnotation))
outputSummaryToTestFormat (OutputSummary s sf _) =
  M.union scalarParams aggregateParams
  where
    scalarParams = foldr collectArgs mempty (M.toList s)

    aggList = groupBy sameArg (M.toList sf)
    aggListByArg = map flattenArg aggList
    aggregateParams = foldr collectAggArgs mempty aggListByArg

    sameArg ((a, _), _) ((b, _), _) = a == b
    flattenArg :: [((Argument, Int), (ArgumentDirection, [Witness]))]
                  -> (Argument, [(Int, ArgumentDirection)])
    flattenArg allFields@(((a, _), _) : _) =
      (a, map flatten' allFields)
    flattenArg [] = error "Foreign.Inference.Analysis.Output.outputSummaryToTestFormat: groupBy made an empty group"
    flatten' ((_, ix), (dir, _)) = (ix, dir)

    dirToAnnot d =
      case d of
        ArgIn -> Nothing
        ArgOut -> Just PAOut
        ArgBoth -> Just PAInOut

    isOut (_, argDir) = argDir == ArgOut

    collectAggArgs (arg, fieldDirections) acc =
      let func = argDefine arg
          funcName = prettySymbol (defName func)
          an = argName arg
      in case argumentFieldCount arg of
        Nothing -> error ("Expected aggregate type in field direction summary " ++ show arg)
        Just fldCnt ->
          case length fieldDirections == fldCnt && all isOut fieldDirections of
            False -> acc
            True ->
              let nv = S.singleton (an, PAOut)
              in MS.insertWith S.union funcName nv acc

    collectArgs (arg, (dir, _)) acc =
      let func = argDefine arg
          funcName = prettySymbol (defName func)
          an = argName arg
      in case dirToAnnot dir of
        Nothing -> acc
        Just annot ->
          let nv = S.singleton (an, annot)
          in MS.insertWith S.union funcName nv acc

{- Note [Pointers In Conditions]

Reading the value of a pointer (the address - not the value in the location
pointed to) makes the pointer an input pointer.  This is because passing in
a non-NULL pointer offers different behavior compared to passing in a NULL
pointer.  Users have control over what action is taken.

This poses a slight problem for some parameters that we might want to treat
as output parameters:

> void foo(int *f) {
>   if(f) {
>     *f = x->y->z;
>   }
> }

According to the above algorithm, @f@ is an in/out parameter.  With the
@trivialBlockHack@ (which defaults to off), this example is treated as an
output paramter.  The trivial block hack says that a pointer parameter in a
conditional is *not* an input parameter iff the successor block in which it is
not null is /trivial/.  Here, trivial is defined as executing no side effects
besides the assignment through @f@.

With this definition, any side effects guarded by an out parameter are
preserved and the out parameter becomes in/out.  In this restricted case,
we allow an exception because we can safely allocate storage and lose nothing
by automating the process.

-}

{- Note [Argument Aliasing]

Aliased arguments require delicate treatment.  Consider a call like

> callee(param1, param1);

where the first parameter of callee is an output parameter and the second
is an input parameter.  If we just processed the arguments left-to-right,
param1 would become an output parameter (since OUT `meet` IN is OUT).  However,
that isn't quite right.  It is used as an input parameter to @callee@, so
it should really be IN/OUT.  We want to treat all of the effects of @callee@ as
happening simultaneously.

We can do that by first checking to see if any arguments are used as input
parameters.  Then process the argument list again to look for output
parameters, performing the standard merge operation.  We could add another
pre-pass for IN/OUT parameters as well.

See test output/aliasedParameterOut.c

-}

