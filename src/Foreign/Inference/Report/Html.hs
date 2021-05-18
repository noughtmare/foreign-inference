{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE OverloadedStrings #-}
module Foreign.Inference.Report.Html (
  SummaryOption(..),
  htmlIndexPage,
  htmlFunctionPage
  ) where

import Control.Arrow ( (&&&) )
import Control.Monad ( forM_, when )
import Data.ByteString.Lazy.Char8 ( ByteString, unpack )
import Data.List ( intercalate, partition, sort )
import Data.Maybe ( mapMaybe, fromMaybe )
import Data.Map ( Map )
import qualified Data.Map as M
import qualified Data.Map.Strict as MS
import Data.Monoid
import Data.Text ( Text )
import qualified Data.Text as T
import Text.Hamlet ( shamlet )
import Text.Shakespeare.Text
import Text.Blaze.Html5 ( toValue, toHtml, (!), Html, AttributeValue )
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as A

import LLVM.Analysis hiding ( toValue, Linkage )
import qualified LLVM.Analysis as LLVM

import Foreign.Inference.Interface
import Foreign.Inference.Interface.Metadata
import Foreign.Inference.Report.Types

import Debug.Trace

-- | Options for generating the HTML summary page
data SummaryOption = LinkDrilldowns -- ^ Include links to the drilldown pages for each function
                   deriving (Eq)

-- | This page is a drilled-down view for a particular function.  The
-- function body is syntax highlighted using the kate syntax
-- definitions.
--
-- FIXME: Provide a table of aggregate stats (counts of each inferred
-- annotation)
--
-- FIXME: It would also be awesome to include call graph information
-- (as in doxygen)
htmlFunctionPage :: InterfaceReport -> Define -> FilePath -> Int -> ByteString -> Html
htmlFunctionPage r f srcFile startLine functionText =
  [shamlet|
$doctype 5
<html>
  <head>
    <title>#{funcName} [function breakdown]
    <link rel=stylesheet href="../style.css" type="text/css">
    <link rel=stylesheet href="../jquery.snippet.css" type="text/css">
    <script type="text/javascript" src="../jquery-1.8.2.min.js">
    <script type="text/javascript" src="../jquery.snippet.js">
    <script type="text/javascript" src="../highlight.js">
  <body>
    Breakdown of #{funcName} (defined in #{srcFile})
    <div>
      <ul>
        $forall arg <- args
          <li>^{drilldownArgumentEntry startLine r arg}
        $if not (null fannots) || not (null uannots)
          <li>&rarr; <span class="code-comment">/* #{show uannots} #{htmlFannots} */</span>
    <p>
      #{funcName} (#{sig}) -> <span class="code-type">#{show fretType}</span>
    <pre id="code" name="code">
      #{preprocessFunction functionText}
    <script type="text/javascript">
      #{H.preEscapedToMarkup (initialScript calledFunctions startLine)}
|]
  where
    funcName = (\(Symbol str) -> str) (defName f)
    allInstructions = concatMap bbStmts (defBody f)
    calledFunctions = foldr (extractCalledFunctionNames aliasReverseIndex) [] allInstructions
    sig = commaSepList args drilldownSignatureArgument
    m = reportModule r
    aliasReverseIndex = foldr indexAliases mempty (modAliases m)
    args = defArgs f
    fretType = case getType f of
      FunTy rt _ _ -> rt
      rtype -> rtype
    allAnnots = manualAnnotations $ reportDependencies r
    uannots = userFunctionAnnotations allAnnots f
    fannots = concatMap (summarizeFunction f) (reportSummaries r)
    htmlFannots = drilldownFunctionAnnotations startLine fannots
    -- fannots = concat [ userFunctionAnnotations allAnnots f
    --                  , concatMap (summarizeFunction f) (reportSummaries r)
    --                  ]

moduleAnnotEntry :: ModuleAnnotation -> Html
moduleAnnotEntry = toHtml . show

indexAliases :: GlobalAlias -> Map Define [GlobalAlias] -> Map Define [GlobalAlias]
indexAliases a m =
  case valValue (aliasTarget a) of
    ValSymbol (SymValDefine f) -> MS.insertWith (++) f [a] m
    ValSymbol (SymValAlias a') -> indexAliases a' m
    _ -> m

-- | Replace tabs with two spaces.  This makes the line number
-- highlighting easier to read.
preprocessFunction :: ByteString -> String
preprocessFunction = foldr replaceTab "" . unpack
  where
    replaceTab '\t' acc = ' ' : ' ' : acc
    replaceTab c acc = c : acc

extractCalledFunctionNames :: Map Define [GlobalAlias] -> Stmt -> [(String, String)] -> [(String, String)]
extractCalledFunctionNames aliasReverseIndex i acc =
  case valueContent' i of
    ValInstr (Call _ _ cv _) -> maybeExtract cv acc
    ValInstr (Invoke _ cv _ _ _) -> maybeExtract cv acc
    _ -> acc
  where
    maybeExtract cv names =
      case valValue (valueContent' cv) of
        (ValSymbol (SymValDefine f)) ->
          case M.lookup f aliasReverseIndex of
            Nothing ->
              let ic = (\(Symbol str) -> str) (defName f)
              in (ic, ic) : names
            Just aliases ->
              let ic = (\(Symbol str) -> str) (defName f)
                  aliasNames = map ((\(Symbol str) -> str) . aliasName) aliases
              in zip aliasNames (repeat ic) ++ names
        _ -> names

-- | This is the content of the script tag included after the code
-- snippet in each drilldown.  It invokes the syntax highlighter and
-- also links all of the functions called to their definitions (if
-- available).
initialScript :: [(String, String)] -> Int -> Text
initialScript calledFuncNames startLine =
  [st|
$(window).bind("load", function() {
  $("pre#code").snippet("c", {style: "emacs", showNum: true, startNum: #{show startLine}});
  initializeHighlighting();
  linkCalledFunctions([#{funcNameList}]);
  });
|]
  where
    toJsTuple (txtName, target) = mconcat ["['", txtName, "', '", target, "']"]
    quotedNames = map toJsTuple calledFuncNames
    funcNameList = intercalate ", " quotedNames


drilldownArgumentEntry :: Int -> InterfaceReport -> Argument -> Html
drilldownArgumentEntry startLine r arg =
  [shamlet|
<span class="code-type">#{show (argType arg)}
  <a href="#" onclick="editor.highlightText('highlight', '#{argumentName}');">
    #{argumentName}
  #{drilldownArgumentAnnotations startLine annots}
|]
  where
    argumentName = argName arg
    annots = concatMap (summarizeArgument arg) (reportSummaries r)

drilldownArgumentAnnotations :: Int -> [(ParamAnnotation, [Witness])] -> Html
drilldownArgumentAnnotations _ [] = return ()
drilldownArgumentAnnotations startLine annots =
  [shamlet| <span class="code-comment"> /* [ #{annotListing} ] */ </span> |]
  where
    annotListing = commaSepList annots mkAnnotLink
    showWL (Witness i s) = do
      l <- instructionToLine i
      return $! mconcat [ "[", show l, ", '", s, "']" ]
    mkAnnotLink (a, witnessLines)
      | null witnessLines = toHtml (show a)
      | otherwise =
        let clickScript = [st|highlightLines(#{show startLine}, [#{intercalate "," (mapMaybe showWL witnessLines)}]);|]
        in [shamlet| <a href="#" onclick="#{H.preEscapedToMarkup clickScript}">#{show a} |]

drilldownFunctionAnnotations :: Int -> [(FuncAnnotation, [Witness])] -> Html
drilldownFunctionAnnotations _ [] = return ()
drilldownFunctionAnnotations startLine annots =
  commaSepList annots mkAnnotLink
  where
    showWL (Witness i s) = do
      l <- instructionToLine i
      return $ mconcat [ "[", show l, ", '", s, "']" ]
    mkAnnotLink (a, witnessLines)
      | null witnessLines = toHtml (show a)
      | otherwise =
        let clickScript = [st|highlightLines(#{show startLine}, [#{intercalate "," (mapMaybe showWL witnessLines)}]);|]
        in [shamlet| <a href="#" onclick="#{H.preEscapedToMarkup clickScript}">#{show a} |]

instructionSrcLoc :: Stmt -> Maybe ValMd
instructionSrcLoc i =
  case filter isSrcLoc (map snd (stmtMd i)) of
    [md] -> Just md
    _ -> Nothing
  where
    isSrcLoc m =
      case m of
        ValMdLoc {} -> True
        _ -> False

instructionToLine :: Stmt -> Maybe Int
instructionToLine i =
  case instructionSrcLoc i of
    Nothing -> Nothing
    Just (ValMdLoc (DebugLoc l _ _ _ _)) -> Just (fromIntegral l)
    _ -> error ("Foreign.Inference.Report.Html.instructionToLine: Expected source location" {- ++ show (stmtMd i) -})

moduleIdentifier :: Module -> String
moduleIdentifier = fromMaybe "Unknown" . modSourceName

-- | Generate an index page listing all of the functions in a module.
-- Each listing shows the parameters and their inferred annotations.
-- Each function name is a link to its source code (if it was found.)
htmlIndexPage :: InterfaceReport -> [SummaryOption] -> Html
htmlIndexPage r opts = H.docTypeHtml $ do
  H.head $ do
    H.title (toHtml pageTitle)
    H.link ! A.href "style.css" ! A.rel "stylesheet" ! A.type_ "text/css"
  H.body $ do
    H.h1 "Module Information"
    H.div ! A.id "module-info" $ do
      stringToHtml "Name: " >> toHtml (moduleIdentifier m)
      H.br
      H.ul $ do
        forM_ mannots moduleAnnotEntry
    H.h1 "Exposed Functions"
    indexPageFunctionListing r (LinkDrilldowns `elem` opts) "exposed-functions" externsWithAliases
    H.h1 "Private Functions"
    indexPageFunctionListing r (LinkDrilldowns `elem` opts) "private-functions" privates
    H.h1 "Annotated Types"
    indexPageTypeListing r ts
  where
    pageTitle :: String
    pageTitle = (moduleIdentifier m) <> " summary report"
    m = reportModule r
    mannots = concatMap (summarizeModule m) (reportSummaries r)
    ts = moduleInterfaceStructTypes m
    (externs, ps) = partition isExtern (modDefines m)
    privates = map tagName ps
    externsWithAliases = map tagName externs ++ exposedAliases

    tagName f = (f, (\(Symbol str) -> str) (defName f))

    isExtern :: (HasVisibility a) => a -> Bool
    isExtern f = isVisible f && isExternLinkage f

    isVisible :: (HasVisibility a) => a -> Bool
    isVisible v =
      case valueVisibility v of
        HiddenVisibility -> False
        _ -> True

    isExternLinkage :: (HasVisibility a) => a -> Bool
    isExternLinkage v =
      case valueLinkage v of
        LLVM.External -> True
        LLVM.AvailableExternally -> True
        LLVM.DLLExport -> True
        LLVM.ExternWeak -> True
        _ -> False

    exposedAliases :: [(Define, String)]
    exposedAliases = mapMaybe externAliasToFunc (modAliases m)

    externAliasToFunc a
      | not (isExtern a) = Nothing
      | otherwise =
        case valValue (aliasTarget a) of
          (ValSymbol (SymValDefine f)) ->
            let internalName = (\(Symbol str) -> str) (defName f)
            in Just (f { defName = aliasName a }, internalName)
          _ -> Nothing

class HasVisibility a where
  valueVisibility :: a -> Visibility
  valueLinkage :: a -> LLVM.Linkage

instance HasVisibility Define where
  valueVisibility = fromMaybe DefaultVisibility . defVisibility
  valueLinkage = fromMaybe External . defLinkage

instance HasVisibility GlobalAlias where
  valueVisibility = fromMaybe DefaultVisibility . aliasVisibility
  valueLinkage = fromMaybe External . aliasLinkage

indexPageTypeListing :: InterfaceReport -> [CType] -> Html
indexPageTypeListing r ts = do
  H.div ! A.id "annotated-types" $ do
    H.ul $ do
      forM_ ts' indexPageAnnotatedType
  where
    ts' = filter (not . null . snd) $ map (id &&& annotateType) (sort ts)
    annotateType t = concatMap (map fst . summarizeType t) (reportSummaries r)

indexPageAnnotatedType :: (CType, [TypeAnnotation]) -> Html
indexPageAnnotatedType (t, annots) = do
  H.li $ do
    H.span $ toHtml (show t)
    stringToHtml " "
    H.span ! A.class_ "code-comment" $ toHtml ("/* " ++ (show annots) ++ " */")


indexPageFunctionListing :: InterfaceReport -> Bool -> AttributeValue -> [(Define, String)] -> Html
indexPageFunctionListing r linkFuncs divId funcs = do
  H.div ! A.id divId $ do
    H.ul $ do
      forM_ funcs (indexPageFunctionEntry r linkFuncs)

indexPageFunctionEntry :: InterfaceReport -> Bool -> (Define, String) -> Html
indexPageFunctionEntry r linkFunc (f, internalName) = do
  H.li $ do
    H.span ! A.class_ "code" $ do
      case r of
        InterfaceReport { reportFunctionBodies = bodies } ->
          case M.lookup f bodies of
            Nothing -> toHtml fname
            Just _ -> do
              let drilldown = mconcat [ "functions/", internalName, ".html" ]
              case linkFunc of
                True -> H.a ! A.href (toValue drilldown) $ toHtml fname
                False -> toHtml fname
        _ -> toHtml fname
      stringToHtml "("
      commaSepList (zip [0..] args) (indexPageArgument r)
      stringToHtml ") -> "
      H.span ! A.class_ "code-type" $ toHtml (show fretType)
      functionAnnotations fannots
  where
    allAnnots = manualAnnotations $ reportDependencies r
    fannots = concat [ userFunctionAnnotations allAnnots f
                     , concatMap (map fst . summarizeFunction f) (reportSummaries r)
                     ]
    fname = (\(Symbol str) -> str) (defName f)
    -- Use a bit of trickery to flag when we need to insert commas
    -- after arguments (so we don't end up with a trailing comma in
    -- the argument list)
    args = defArgs f
    fretType = case getType f of
      FunTy rt _ _ -> rt
      rtype -> rtype

drilldownSignatureArgument :: Argument -> Html
drilldownSignatureArgument arg =
  [shamlet|
<span class="code-type">#{paramType}</span> #{paramName}
|]
  where
    paramType = show (argType arg)
    paramName = argName arg

indexPageArgument :: InterfaceReport -> (Int, Argument) -> Html
indexPageArgument r (ix, arg) = do
  H.span ! A.class_ "code-type" $ toHtml paramType
  stringToHtml " " >> toHtml paramName >> stringToHtml " " >> indexArgumentAnnotations annots
  where
    paramType = show (argType arg)
    paramName = argName arg
    allAnnots = manualAnnotations $ reportDependencies r
    annots = concat [ userParameterAnnotations allAnnots (argDefine arg) ix
                    , concatMap (map fst . summarizeArgument arg) (reportSummaries r)
                    ]

indexArgumentAnnotations :: [ParamAnnotation] -> Html
indexArgumentAnnotations [] = return ()
indexArgumentAnnotations annots =
  H.span ! A.class_ "code-comment" $ do
    stringToHtml " /* ["
    commaSepList annots (toHtml . show)
    stringToHtml "] */"

functionAnnotations :: [FuncAnnotation] -> Html
functionAnnotations [] = return ()
functionAnnotations annots =
  H.span ! A.class_ "code-comment" $
    stringToHtml " /* [" >> commaSepList annots (toHtml . show) >> stringToHtml "] */"

-- Helpers


-- | Print out a comma-separated list of items (given a function to
-- turn those items into Html).  This handles the annoying details of
-- not accidentally printing a trailing comma.
commaSepList :: [a] -> (a -> Html) -> Html
commaSepList itms f =
  forM_ (zip itms commaTags) $ \(itm, tag) -> do
    f itm
    when tag (stringToHtml ", ")
  where
    commaTags = reverse $ False : replicate (length itms - 1) True

stringToHtml :: String -> Html
stringToHtml = toHtml
