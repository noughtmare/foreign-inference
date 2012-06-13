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

import Data.List ( elemIndex, foldl', intercalate )
import Data.List.Ordered ( union )
import Data.Map ( Map )
import qualified Data.Map as M
import Data.Maybe ( mapMaybe )
import Data.Monoid

import LLVM.Analysis
import LLVM.Analysis.AccessPath
import LLVM.Analysis.ClassHierarchy
import LLVM.Analysis.PointsTo

-- | This isn't a true points-to analysis because it is an
-- under-approximation.  However, that is sufficient for this library.
instance PointsToAnalysis IndirectCallSummary where
  mayAlias _ _ _ = True
  pointsTo = indirectCallInitializers
  resolveIndirectCall = indirectCallTargets

data IndirectCallSummary =
  ICS { abstractPathInitializers :: !(Map AbstractAccessPath [Value])
        -- ^ Function initializers assigned to fields of types
      , concreteValueInitializers :: !(Map GlobalVariable [Value])
        -- ^ Explicit values assigned to global variables, either at
        -- initialization time or through a later assignment.
      , argumentInitializers :: !(Map (Function, Int) [Value])
        -- ^ A map of all of the known initializers (Functions or
        -- External functions) passed as the ix'th argument of the
        -- Function that is the key of the map.
      , fieldArgDependencies :: !(Map AbstractAccessPath [(Function, Int)])
      , globalArgDependencies :: !(Map GlobalVariable [(Function, Int)])
      , resolverCHA :: CHA
        -- ^ The class hierarchy analysis
      }

instance Show IndirectCallSummary where
  show (ICS api cbi _ _ _ _) = concat [ "Abstract Path Initializers\n"
                                        , unlines $ map showAPI (M.toList api)
                                        , "\nConcrete Value Initializers\n"
                                        , unlines $ map showCBI (M.toList cbi)
                                        ]
    where
      showAPI (aap, vs) = concat [ " * ", show aap, ": ", intercalate ", " (map (show . valueName) vs)]
      showCBI (gv, vs) = concat [ " * ", show (globalVariableName gv), ": ", intercalate ", " (map (show . valueName) vs)]

emptySummary :: Module -> Map GlobalVariable [Value] -> IndirectCallSummary
emptySummary m cvis =
  ICS mempty cvis mempty mempty mempty cha
  where
    cha = runCHA m

indirectCallInitializers :: IndirectCallSummary -> Value -> [Value]
indirectCallInitializers s v =
  case valueContent' v of
    InstructionC i -> maybe [] id $ do
      accPath <- accessPath i
      let absPath = abstractAccessPath accPath
      case valueContent' (accessPathBaseValue accPath) of
        GlobalVariableC gv@GlobalVariable { globalVariableInitializer = Just initVal } ->
          case followAccessPath absPath initVal of
            Nothing -> return $! globalVarLookup s gv
            accPathVal -> fmap return accPathVal
        _ -> return $! absPathLookup s absPath
    _ -> []

-- | Resolve the targets of an indirect call instruction.  This works
-- with both C++ virtual function dispatch and some other common
-- function pointer call patterns.  It is unsound and incomplete.
--
-- FIXME: Make this capable of returning external functions...
-- expected value is low.
indirectCallTargets :: IndirectCallSummary -> Instruction -> [Function]
indirectCallTargets ics i =
  case resolveVirtualCallee (resolverCHA ics) i of
    Just fs -> fs
    Nothing ->
      case i of
        CallInst { callFunction = f } ->
          mapMaybe toFunction $ indirectCallInitializers ics f
        InvokeInst { invokeFunction = f } ->
          mapMaybe toFunction $ indirectCallInitializers ics f
        _ -> []
  where
    toFunction v =
      case valueContent' v of
        FunctionC f -> Just f
        _ -> Nothing

-- | Look up the initializers for this abstract access path.  The key
-- here is that we get both the initializers we know for this path,
-- along with initializers for *suffixes* of the path.  For example,
-- if the path is a.b.c.d, we also care about initializers for b.c.d
-- (and c.d).  The recursive walk is in the reducedPathResults
-- segment.
absPathLookup :: IndirectCallSummary -> AbstractAccessPath -> [Value]
absPathLookup s absPath = storeInits `union` argInits `union` reducedPathResults
  where
    storeInits = M.findWithDefault [] absPath (abstractPathInitializers s)
    argDeps = M.findWithDefault [] absPath (fieldArgDependencies s)
    argInits = concatMap (\x -> M.findWithDefault [] x (argumentInitializers s)) argDeps
    reducedPathResults =
      case reduceAccessPath absPath of
        Nothing -> []
        Just rpath -> absPathLookup s rpath

globalVarLookup :: IndirectCallSummary -> GlobalVariable -> [Value]
globalVarLookup s gv = concreteInits `union` argInits
  where
    concreteInits = M.findWithDefault [] gv (concreteValueInitializers s)
    argDeps = M.findWithDefault [] gv (globalArgDependencies s)
    argInits = concatMap (\x -> M.findWithDefault [] x (argumentInitializers s)) argDeps

-- | Run the initializer analysis: a cheap pass to identify a subset
-- of possible function pointers that object fields can point to.
identifyIndirectCallTargets :: Module -> IndirectCallSummary
identifyIndirectCallTargets m =
  foldl' (flip recordInitializers) s0 allInsts
  where
    s0 = emptySummary m (M.fromList globalsWithInits)
    allBlocks = concatMap functionBody $ moduleDefinedFunctions m
    allInsts = concatMap basicBlockInstructions allBlocks
    globalsWithInits = foldr extractGlobalsWithInits [] (moduleGlobalVariables m)

extractGlobalsWithInits :: GlobalVariable
                           -> [(GlobalVariable, [Value])]
                           -> [(GlobalVariable, [Value])]
extractGlobalsWithInits gv acc =
  case globalVariableInitializer gv of
    Nothing -> acc
    Just i -> (gv, [i]) : acc

recordInitializers :: Instruction -> IndirectCallSummary -> IndirectCallSummary
recordInitializers i s =
  case i of
    StoreInst { storeValue = sv, storeAddress = sa } ->
      case valueContent' sv of
        FunctionC _ -> maybeRecordInitializer i sv sa s
        ExternalFunctionC _ -> maybeRecordInitializer i sv sa s
        ArgumentC a ->
          let f = argumentFunction a
              Just ix = elemIndex a (functionParameters f)
          in recordArgInitializer i f ix sa s
        _ -> s
    CallInst { callFunction = (valueContent' -> FunctionC f)
             , callArguments = args
             } ->
      let ixArgs = zip [0..] $ map fst args
      in foldl' (recordArgFuncInit f) s ixArgs
    InvokeInst { invokeFunction = (valueContent' -> FunctionC f)
               , invokeArguments = args
               } ->
      let ixArgs = zip [0..] $ map fst args
      in foldl' (recordArgFuncInit f) s ixArgs
    _ -> s

-- | If an actual argument has a Function (or ExternalFunction) as its
-- value, record that as a value as associated with the ix'th argument
-- of the callee.
recordArgFuncInit :: Function
                     -> IndirectCallSummary
                     -> (Int, Value)
                     -> IndirectCallSummary
recordArgFuncInit f s (ix, arg) =
  case valueContent' arg of
    FunctionC _ ->
      s { argumentInitializers =
             M.insertWith union (f, ix) [arg] (argumentInitializers s)
        }
    ExternalFunctionC _ ->
      s { argumentInitializers =
             M.insertWith union (f, ix) [arg] (argumentInitializers s)
        }
    _ -> s

recordArgInitializer :: Instruction
                        -> Function
                        -> Int
                        -> Value
                        -> IndirectCallSummary
                        -> IndirectCallSummary
recordArgInitializer i f ix sa s =
  case valueContent' sa of
    GlobalVariableC gv ->
      s { globalArgDependencies =
             M.insertWith' union gv [(f, ix)] (globalArgDependencies s)
        }
    _ ->
      case accessPath i of
        Nothing -> s
        Just accPath ->
          let absPath = abstractAccessPath accPath
          in s { fieldArgDependencies =
                    M.insertWith' union absPath [(f, ix)] (fieldArgDependencies s)
               }

-- | Initializers here (sv) are only functions (external or otherwise)
maybeRecordInitializer :: Instruction -> Value -> Value
                          -> IndirectCallSummary
                          -> IndirectCallSummary
maybeRecordInitializer i sv sa s =
  case valueContent' sa of
    GlobalVariableC gv ->
      s { concreteValueInitializers =
             M.insertWith' union gv [sv] (concreteValueInitializers s)
        }
    _ ->
      case accessPath i of
        Nothing -> s
        Just accPath ->
          let absPath = abstractAccessPath accPath
          in s { abstractPathInitializers =
                    M.insertWith' union absPath [sv] (abstractPathInitializers s)
               }