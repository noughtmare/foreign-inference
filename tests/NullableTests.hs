module Main ( main ) where

import qualified Data.Map as M
import Data.Monoid
import qualified Data.Set as S
import System.FilePath ( (<.>) )
import System.Environment ( getArgs, withArgs )
import Test.HUnit ( assertEqual )
import qualified Data.ByteString as B
import Control.Lens (to)

import LLVM.Analysis
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.PointsTo
import LLVM.Analysis.Util.Testing
import Data.LLVM.BitCode
import Text.LLVM.Resolve

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Nullable
import Foreign.Inference.Analysis.Return
import Foreign.Inference.Analysis.Util.CompositeSummary

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/nullable/*.c"
        [infile] -> infile
  ds <- loadDependencies ["tests/nullable"] ["base"]
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeNullable ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations parser testDescriptors
  where
    parser _f h = fmap (resolve . (\(Right x) -> x)) . parseBitCode =<< B.hGetContents h

analyzeNullable ds m =
  nullSummaryToTestFormat (_nullableSummary res)
  where
    pta = identifyIndirectCallTargets m
    cg = callGraph m pta []
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifyReturns ds returnSummary
               , identifyNullable ds nullableSummary returnSummary (errorHandlingSummary . to Just)
               ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = callGraphSCCTraversal cg analysisFunc mempty
