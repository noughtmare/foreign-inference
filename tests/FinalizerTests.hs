module Main ( main ) where

import Data.Map ( Map )
import Data.Monoid
import Data.Set ( Set )
import System.FilePath ( (<.>) )
import System.Environment ( getArgs, withArgs )
import Test.HUnit ( assertEqual )
import Data.ByteString (hGetContents)

import LLVM.Analysis
import LLVM.Analysis.CallGraph
import LLVM.Analysis.CallGraphSCCTraversal
import LLVM.Analysis.Util.Testing
import Data.LLVM.BitCode
import Text.LLVM.Resolve

import Foreign.Inference.Interface
import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.Finalize
import Foreign.Inference.Analysis.IndirectCallResolver
import Foreign.Inference.Analysis.Util.CompositeSummary

import System.IO (hSetBuffering, BufferMode (NoBuffering), stdout)

main :: IO ()
main = do
  args <- getArgs
  hSetBuffering stdout NoBuffering
  let pattern = case args of
        [] -> "tests/finalize/*.c"
        [infile] -> infile
        _ -> error "At most one argument allowed"
  ds <- loadDependencies ["tests/finalize"] []
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = analyzeFinalize ds
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations parser testDescriptors
  where
    parser _f h = fmap (resolve . (\(Right x) -> x)) . parseBitCode =<< hGetContents h

analyzeFinalize :: DependencySummary -> Module -> Map String (Set String)
analyzeFinalize ds m =
  finalizerSummaryToTestFormat (_finalizerSummary res)
  where
    ics = identifyIndirectCallTargets m
    cg = callGraph m ics []
    analyses :: [ComposableAnalysis AnalysisSummary FunctionMetadata]
    analyses = [ identifyFinalizers ds ics finalizerSummary ]
    analysisFunc = callGraphComposeAnalysis analyses
    res = callGraphSCCTraversal cg analysisFunc mempty
