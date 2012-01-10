{-# LANGUAGE OverloadedStrings #-}
module Foreign.Inference.Report.FunctionText (
  getFunctionText
  ) where

import Control.Applicative ( many )
import Data.Attoparsec.Text ( Parser )
import qualified Data.Attoparsec.Text as P
import qualified Data.ByteString.Char8 as BSC
import Data.Text.Lazy ( Text )
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.Encoding as T
import qualified Data.Text as TS
import qualified Data.Text.Encoding as TS
import System.FilePath

import Codec.Archive
import Data.LLVM

isolator :: Parser TS.Text
isolator = do
  -- We want the prefix of the function up until we see the opening
  -- curly brace.
  pfx <- P.takeWhile (/= '{')

  -- Now just match curly braces in a standard context-free way.
  -- FIXME: Ignore string literals, char literals, and comments
  body <- matchedBraces
  -- Ignore the rest
  _ <- P.takeLazyText
  return (pfx `TS.append` body)

matchedBraces :: Parser TS.Text
matchedBraces = do
  _ <- P.char '{'
  content <- many contentAndSubBody
  _ <- P.char '}'
  return $ TS.concat ["{", TS.concat content, "}"]

contentAndSubBody :: Parser TS.Text
contentAndSubBody = do
  pfx <- P.takeWhile (\c -> c /= '{' && c /= '}')
  P.choice [ nest pfx, blockEnd pfx ]
  where
    blockEnd :: TS.Text -> Parser TS.Text
    blockEnd pfx = do
      case TS.null pfx of
        True -> fail "fail"
        False -> return pfx
    nest pfx = do
      body <- matchedBraces
      rest <- contentAndSubBody
      return $ TS.concat [ pfx, body, rest ]

-- | Make a best effort to find the implementation of the given
-- Function in its associated source archive.  The lookup is based on
-- debugging metadata (and will fail early if there is none).
--
-- From there, the starting line number of the function will be used
-- to try to isolate the body of the function in the file.
getFunctionText :: ArchiveIndex -> Function -> Maybe (FilePath, Int, TS.Text)
getFunctionText a func = do
  let [md] = functionMetadata func
      md' = metaValueContent md
      line = metaSubprogramLine md'
  ctxt <- metaSubprogramContext md'

  let ctxt' = metaValueContent ctxt
      f = metaFileSourceFile ctxt'
      d = metaFileSourceDir ctxt'
      absSrcFile = BSC.unpack d </> BSC.unpack f

  bs <- entryContentSuffix a absSrcFile
  let t = T.decodeUtf8 bs
      fident = identifierContent $ functionName func
      fnameText = T.fromStrict $ TS.decodeUtf8 fident
      -- f starts on line number @line@.  We need to seek to that line
      -- and then search *backwards* for the function name (so we can
      -- get the arguments, too).
      (beforeCodeStart, codeStart) = splitAt (fromIntegral line) $ T.lines t
      (interestingCode, _) =
        foldr (findFuncName fnameText) (codeStart, True) beforeCodeStart

      -- f starts on line number line, so drop all of the lines up to
      -- there.  Then recombine the rest into a single Text that we
      -- can "parse".
      fileChunk = T.unlines interestingCode
      functionText = P.parseOnly isolator (T.toStrict fileChunk)
      mkTuple txt = Just (absSrcFile, fromIntegral line, txt)
  either (const Nothing) mkTuple functionText
  -- Now match curly braces and only keep what we accumulate until it
  -- drops back to zero.

-- Search backwards for the function name from the opening curly brace
-- using foldr.  Stop searching (and collecting chunks) when we find
-- the line with the function name in it.
--
-- This function may miss the return type, but that isn't a huge deal.
findFuncName :: Text -> Text -> ([Text], Bool) -> ([Text], Bool)
findFuncName _ _ a@(_, False) = a
findFuncName fname line (acc, True) =
  case fname `T.isInfixOf` line of
    False -> (line : acc, True)
    True -> (line : acc, False)