{-
Authors: Makarius Wenzel (2018)

Formal output messages, with PIDE (Prover IDE) support.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}

module SAD.Core.Message (Kind (..), PIDE, pideContext, pideActive,
  entityMarkup,
  Report, ReportText, reportsText, reportText, reports, report,
  trimText, output, error, outputMain, outputExport, outputForTheL,
  outputParser, outputReason, outputThesis, outputSimp,
  errorExport, errorParser
) where

import Prelude hiding (error)
import qualified Prelude (error)
import System.Environment
import Control.Monad
import Data.Maybe
import Data.ByteString (ByteString)
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Char8 as Char8
import qualified Data.ByteString.UTF8 as UTF8

import SAD.Core.SourcePos (SourcePos)
import qualified SAD.Core.SourcePos as SourcePos

import Isabelle.Library as Isabelle
import qualified Isabelle.Value as Value
import qualified Isabelle.Markup as Markup
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML
import qualified Isabelle.Byte_Message as Byte_Message


-- message kind

data Kind =
  STATE | WRITELN | INFORMATION | TRACING | WARNING | LEGACY | ERROR

instance Show Kind where
  show WARNING = "Warning"
  show LEGACY = "Legacy feature"
  show ERROR = "Error"
  show _ = ""


-- PIDE context

data PIDE = PIDE {pideID :: String, pideFile :: String, pideShift :: Int}

pideContext :: IO (Maybe PIDE)
pideContext = do
  pide <- lookupEnv "NAPROCHE_PIDE"
  file <- fromMaybe "" <$> lookupEnv "NAPROCHE_POS_FILE"
  shift <- fromMaybe "0" <$> lookupEnv "NAPROCHE_POS_SHIFT"
  case (pide, Value.parse_int shift) of
    (Nothing, _) -> return Nothing
    (Just "", _) -> return Nothing
    (_, Nothing) -> return Nothing
    (Just id, Just i) -> return $ Just (PIDE id file i)

pideActive :: IO Bool
pideActive = isJust <$> pideContext


-- PIDE messages

kindXML :: Kind -> String
kindXML STATE = Markup.stateN
kindXML WRITELN = Markup.writelnN
kindXML INFORMATION = Markup.informationN
kindXML TRACING = Markup.tracingN
kindXML WARNING = Markup.warningN
kindXML LEGACY = Markup.legacyN
kindXML ERROR = Markup.errorN

posProperties :: PIDE -> SourcePos -> [(String, String)]
posProperties PIDE{pideID, pideFile, pideShift} pos =
  (if null pideID then [] else [(Markup.idN, pideID)]) ++
  (if null file then [] else [(Markup.fileN, file)]) ++
  (if line <= 0 then [] else [(Markup.lineN, Value.print_int line)]) ++
  (if offset <= 0 then [] else [(Markup.offsetN, Value.print_int offset)]) ++
  (if endOffset <= 0 then [] else [(Markup.end_offsetN, Value.print_int endOffset)])
  where
    file =
      case SourcePos.sourceFile pos of
        "" -> pideFile
        file -> file
    line = if null file then 0 else SourcePos.sourceLine pos
    shift i = if i <= 0 then i else i + pideShift
    offset = shift $ SourcePos.sourceOffset pos
    endOffset = shift $ SourcePos.sourceEndOffset pos

posDefProperties :: PIDE -> SourcePos -> [(String, String)]
posDefProperties pide = map (\(a, b) -> ("def_" ++ a, b)) . posProperties pide

entityProperties :: PIDE -> Bool -> Int -> SourcePos -> [(String, String)]
entityProperties pide def serial pos =
  if def then (Markup.defN, Value.print_int serial) : posProperties pide pos
  else (Markup.refN, Value.print_int serial) : posDefProperties pide pos

entityMarkup :: PIDE -> String -> String -> Bool -> Int -> SourcePos -> Markup.T
entityMarkup pide kind name def serial pos =
    Markup.properties (entityProperties pide def serial pos) (Markup.entity kind name)

xmlMessage :: PIDE -> String -> Kind -> SourcePos -> String -> XML.Tree
xmlMessage pide origin kind pos msg =
  XML.Elem ((kindXML kind, props), [XML.Text msg])
  where
    props0 = posProperties pide pos
    props = if null origin then props0 else ("origin", origin) : props0

pideMessage :: String -> ByteString
pideMessage = ByteString.concat . Byte_Message.make_line_message . UTF8.fromString


-- PIDE markup reports

type Report = (SourcePos, Markup.T)
type ReportText = (Report, String)

reportsText :: [ReportText] -> IO ()
reportsText args = do
  pide <- pideContext
  when (isJust pide && not (null args)) $ Char8.putStrLn $ pideMessage $ YXML.string_of $
    XML.Elem (Markup.report,
      map (\((pos, markup), txt) ->
        let
          markup' = Markup.properties (posProperties (fromJust pide) pos) markup
          body = if null txt then [] else [XML.Text txt]
        in XML.Elem (markup', body)) args)

reportText :: SourcePos -> Markup.T -> String -> IO ()
reportText pos markup txt = reportsText [((pos, markup), txt)]

reports :: [Report] -> IO ()
reports = reportsText . map (, "")

report :: SourcePos -> Markup.T -> IO ()
report pos markup = reports [(pos, markup)]


-- output

trimText :: String -> String
trimText = Isabelle.trim_line

messageBytes :: Maybe PIDE -> String -> Kind -> SourcePos -> String -> ByteString
messageBytes pide origin kind pos msg =
  if isJust pide then
    pideMessage $ YXML.string_of $ xmlMessage (fromJust pide) origin kind pos msg
  else
    UTF8.fromString
      ((if null origin then "" else "[" ++ origin ++ "] ") ++
       (case show kind of "" -> "" ; s -> s ++ ": ") ++
       (case show pos of "" -> ""; s -> s ++ "\n") ++ msg)

output :: String -> Kind -> SourcePos -> String -> IO ()
output origin kind pos msg = do
  pide <- pideContext
  Char8.putStrLn $ messageBytes pide origin kind pos msg

error :: String -> SourcePos -> String -> IO a
error origin pos msg = do
  pide <- pideContext
  errorWithoutStackTrace $ UTF8.toString (messageBytes pide origin ERROR pos msg)


-- specific messages

outputMain, outputExport, outputForTheL, outputParser, outputReason, outputSimp, outputThesis
  :: Kind -> SourcePos -> String -> IO ()
outputMain = output "Main"
outputExport = output "Export"
outputForTheL = output "ForTheL"
outputParser = output "Parser"
outputReason = output "Reasoner"
outputSimp = output "Simplifier"
outputThesis = output "Thesis"

errorExport = error "Export"
errorParser = error "Parser"
