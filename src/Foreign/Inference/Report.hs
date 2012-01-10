{-# LANGUAGE OverloadedStrings #-}
-- | This module provides some functions to generate HTML reports for
-- a Module and its inferred annotations.  This module handles the
-- extraction of source code (from tarballs/zip files) and mapping
-- Functions to their associated source code using various heuristics.
--
-- FIXME: The drilldowns for functions may be overwritten by functions
-- of the same name... this probably won't be a problem in practice
-- since there would be linker errors of that happens.
module Foreign.Inference.Report (
  -- * Types
  InterfaceReport,
  -- * Functions
  compileReport,
  writeHTMLReport
  ) where

import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Map as M
import Data.Text ( Text )
import System.Directory ( copyFile, createDirectoryIfMissing )
import System.FilePath
import Text.Blaze.Renderer.Utf8 ( renderHtml )

import Codec.Archive
import Data.LLVM
import Foreign.Inference.Interface
import Foreign.Inference.Report.FunctionText
import Foreign.Inference.Report.Html
import Foreign.Inference.Report.Types

import Paths_foreign_inference


-- | Write the given report into the given directory.  An index.html file
-- will be placed in the directory and subdirectories within that will
-- contain the actual content.
--
-- An error will be thrown if the given path exists and is not a
-- directory.  The directory will be created if it does not exist.
writeHTMLReport :: InterfaceReport -> FilePath -> IO ()
writeHTMLReport r dir = do
  let indexFile = dir </> "index.html"
      indexPage = htmlIndexPage r

  -- Create the directory tree for the report
  createDirectoryIfMissing True dir
  createDirectoryIfMissing True (dir </> "functions")

  -- Write out an index page
  LBS.writeFile indexFile (renderHtml indexPage)
  -- Write out the individual function listings
  mapM_ (writeFunctionBodyPage r dir) $ M.toList (reportFunctionBodies r)
  -- Copy over static resources (like css and js)
  mapM_ (installStaticFile dir) [ "style.css"
                                , "hk-espresso.css"
                                , "hk-pyg.css"
                                , "hk-tango.css"
                                , "hk-kate.css"
                                , "jquery-1.7.1.js"
                                , "highlight.js"
                                ]

-- | Install a file from the project share directory to the target
-- report directory (top-level).
installStaticFile :: FilePath -> FilePath -> IO ()
installStaticFile dir name = do
  file <- getDataFileName ("static" </> name)
  copyFile file (dir </> name)

writeFunctionBodyPage :: InterfaceReport
                         -> FilePath
                         -> (Function, (FilePath, Int, Text))
                         -> IO ()
writeFunctionBodyPage r dir (f, (srcFile, startLine, body)) = do
  let funcName = BS8.unpack (identifierContent (functionName f))
      filename = dir </> "functions" </> funcName <.> "html"
      functionPage = htmlFunctionPage r f srcFile startLine body

  LBS.writeFile filename (renderHtml functionPage)

-- | Given a Module, the properties that have been inferred about it,
-- and an archive of its source, make a best-effort to construct an
-- informative report of the results.
compileReport :: Module -> ArchiveIndex -> [ModuleSummary] -> InterfaceReport
compileReport m a = InterfaceReport m bodies a
  where
    fs = moduleDefinedFunctions m
    bodies = foldr bodyExtractor M.empty fs
    bodyExtractor f acc =
      case getFunctionText a f of
        Nothing -> acc
        Just b -> M.insert f b acc