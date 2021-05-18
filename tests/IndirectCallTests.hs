module Main ( main ) where

import qualified Data.Foldable as F
import Data.Monoid
import Data.Set ( Set )
import qualified Data.Set as S
import System.FilePath ( (<.>) )
import System.Environment ( getArgs, withArgs )
import Test.HUnit ( assertEqual )
import Data.ByteString ( hGetContents )

import LLVM.Analysis
import LLVM.Analysis.Util.Testing
import Data.LLVM.BitCode
import Text.LLVM.Resolve

import Foreign.Inference.Preprocessing
import Foreign.Inference.Analysis.IndirectCallResolver

main :: IO ()
main = do
  args <- getArgs
  let pattern = case args of
        [] -> "tests/indirect-calls/*.c"
        [infile] -> infile
        _ -> error "At most one argument allowed"
  let testDescriptors = [ TestDescriptor { testPattern = pattern
                                         , testExpectedMapping = (<.> "expected")
                                         , testResultBuilder = checkIndirectTargets
                                         , testResultComparator = assertEqual
                                         }
                        ]
  withArgs [] $ testAgainstExpected requiredOptimizations parser testDescriptors
  where
    parser _f h = fmap (resolve . (\(Right x) -> x)) . parseBitCode =<< hGetContents h

-- | Find the first indirect call in the Module and return the set of
-- functions it could possibly point to.
checkIndirectTargets :: Module -> Set String
checkIndirectTargets m =
  foldr targetNames mempty (indirectCallInitializers ics callee)
  where
    fs = modDefines m
    Just i = F.find isIndirectCallInst (concatMap defStmts fs)
    Call _ _ callee _ = stmtInstr i
    ics = identifyIndirectCallTargets m

isIndirectCallInst :: Stmt -> Bool
isIndirectCallInst i =
  case stmtInstr i of
    Call _ _ cf _ ->
      case valValue (valueContent' cf) of
        (ValSymbol (SymValDefine _)) -> False
        (ValSymbol (SymValDeclare _)) -> False
        _ -> True
    _ -> False

targetNames :: Value -> Set String -> Set String
targetNames v = S.insert n
  where
    Just n = valName v
