module Main ( main ) where

import Data.Monoid
import System.Environment ( getArgs, withArgs )
import System.FilePath ( (<.>) )
import Test.HUnit ( assertEqual )
import qualified Data.ByteString as B

import LLVM.Analysis
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Util.Testing
import Data.LLVM.BitCode
import Text.LLVM.Resolve

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.Array
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Util.CompositeSummary

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/arrays/*.c"
        [infile] -> infile
  ds <- loadDependencies' [] ["tests/arrays"] ["base"]
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeArrays ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations bcParser testDescriptors
  where
    bcParser _f h = fmap (resolve . fromRight) . parseBitCode =<< B.hGetContents h

fromRight (Right x) = x

analyzeArrays ds m =
  arraySummaryToTestFormat (_arraySummary res)
  where
    pta = identifyIndirectCallTargets m
    cg = callGraph m pta []
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifyArrays ds arraySummary ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = callGraphSCCTraversal cg analysisFunc mempty
