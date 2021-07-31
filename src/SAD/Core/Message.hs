{-
Authors: Makarius Wenzel (2018)

Formal output messages, with PIDE (Prover IDE) support.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}

module SAD.Core.Message (
  PIDE, pideContext, pideActive,
  initThread, exitThread, consoleThread,
  Kind (..), entityMarkup,
  Report, ReportString, reportsString, reportString, reports, report,
  trimString, output, error, outputMain, outputExport, outputForTheL,
  outputParser, outputReasoner, outputThesis, outputSimplifier, outputTranslate,
  errorExport, errorParser
) where

import Prelude hiding (error)
import System.Environment
import Control.Monad
import Data.Maybe
import Data.IORef
import System.IO.Unsafe
import Data.Map.Strict (Map)
import Data.Bifunctor (bimap)
import qualified Data.Map.Strict as Map
import qualified Data.ByteString.Char8 as Char8
import Control.Concurrent (ThreadId)
import qualified Control.Concurrent as Concurrent

import SAD.Core.SourcePos (SourcePos)
import qualified SAD.Core.SourcePos as SourcePos

import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Value as Value
import qualified Isabelle.Markup as Markup
import qualified Isabelle.UTF8 as UTF8
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Naproche as Naproche
import Isabelle.Library (make_bytes, trim_line)


-- PIDE thread context

data PIDE = PIDE {pideID :: Bytes, pideFile :: Bytes, pideShift :: Int}
type Channel = [Bytes] -> IO ()
data Context = Context {pide :: Maybe PIDE, channel :: Channel}

defaultChannel :: Channel
defaultChannel = Char8.putStrLn . Bytes.unmake . Bytes.concat

defaultContext :: Context
defaultContext = Context Nothing defaultChannel


-- global state

type Threads = Map ThreadId Context

{-# NOINLINE globalState #-}
globalState :: IORef Threads
globalState = unsafePerformIO (newIORef Map.empty)

getContext :: IO Context
getContext = do
  id <- Concurrent.myThreadId
  threads <- readIORef globalState
  return (fromMaybe defaultContext (Map.lookup id threads))

updateState :: (ThreadId -> Threads -> Threads) -> IO ()
updateState f = do
  id <- Concurrent.myThreadId
  atomicModifyIORef' globalState (\threads -> (f id threads, ()))


-- PIDE context

pideContext :: IO (Maybe PIDE)
pideContext = pide <$> getContext

pideActive :: IO Bool
pideActive = isJust <$> pideContext


-- init/exit thread context

initThread :: Properties.T -> Channel -> IO ()
initThread props channel = do
  updateState (\id -> Map.insert id (Context pideContext channel))
  where
    property parse = Properties.get_value parse props
    pideProperty = property (\x -> guard (not $ Bytes.null x) >> pure x) Naproche.naproche_pide
    fileProperty = property Just Naproche.naproche_pos_file
    shiftProperty = property Value.parse_int Naproche.naproche_pos_shift
    pideContext =
      case (pideProperty, fileProperty, shiftProperty) of
        (Just pide, Just file, Just shift) -> Just (PIDE pide file shift)
        _ -> Nothing

exitThread :: IO ()
exitThread = updateState Map.delete

consoleThread :: IO ()
consoleThread = do
  env <- getEnvironment
  initThread (map (bimap make_bytes make_bytes) env) defaultChannel


-- PIDE messages

data Kind =
  STATE | WRITELN | INFORMATION | TRACING | WARNING | LEGACY | ERROR

instance Show Kind where
  show WARNING = "Warning"
  show LEGACY = "Legacy feature"
  show ERROR = "Error"
  show _ = ""

kindXML :: Kind -> Bytes
kindXML STATE = Markup.stateN
kindXML WRITELN = Markup.writelnN
kindXML INFORMATION = Markup.informationN
kindXML TRACING = Markup.tracingN
kindXML WARNING = Markup.warningN
kindXML LEGACY = Markup.legacyN
kindXML ERROR = Markup.errorN

posProperties :: PIDE -> SourcePos -> Properties.T
posProperties PIDE{pideID, pideFile, pideShift} pos =
  (if Bytes.null pideID then [] else [(Markup.idN, pideID)]) ++
  (if Bytes.null file then [] else [(Markup.fileN, file)]) ++
  (if line <= 0 then [] else [(Markup.lineN, Value.print_int line)]) ++
  (if offset <= 0 then [] else [(Markup.offsetN, Value.print_int offset)]) ++
  (if endOffset <= 0 then [] else [(Markup.end_offsetN, Value.print_int endOffset)])
  where
    file = if Bytes.null $ SourcePos.sourceFile pos then pideFile else SourcePos.sourceFile pos
    line = if Bytes.null file then 0 else SourcePos.sourceLine pos
    shift i = if i <= 0 then i else i + pideShift
    offset = shift $ SourcePos.sourceOffset pos
    endOffset = shift $ SourcePos.sourceEndOffset pos

posDefProperties :: PIDE -> SourcePos -> Properties.T
posDefProperties pide = map (\(a, b) -> ("def_" <> a, b)) . posProperties pide

entityProperties :: PIDE -> Bool -> Int -> SourcePos -> Properties.T
entityProperties pide def serial pos =
  if def then (Markup.defN, Value.print_int serial) : posProperties pide pos
  else (Markup.refN, Value.print_int serial) : posDefProperties pide pos

entityMarkup :: PIDE -> Bytes -> Bytes -> Bool -> Int -> SourcePos -> Markup.T
entityMarkup pide kind name def serial pos =
    Markup.properties (entityProperties pide def serial pos) (Markup.entity kind name)

xmlMessage :: PIDE -> Bytes -> Kind -> SourcePos -> Bytes -> XML.Tree
xmlMessage pide origin kind pos msg =
  XML.Elem ((kindXML kind, props), [XML.Text msg])
  where
    props0 = posProperties pide pos
    props = if Bytes.null origin then props0 else (Naproche.origin, make_bytes origin) : props0

pideMessage :: Bytes -> [Bytes]
pideMessage = Byte_Message.make_line_message


-- PIDE markup reports

type Report = (SourcePos, Markup.T)
type ReportString = (Report, String)

reportsString :: [ReportString] -> IO ()
reportsString args = do
  context <- getContext
  when (isJust (pide context) && not (null args)) $
    channel context $ pideMessage $ YXML.string_of $
      XML.Elem (Markup.report,
        map (\((pos, markup), txt) ->
          let
            markup' = Markup.properties (posProperties (fromJust (pide context)) pos) markup
            body = if null txt then [] else [XML.Text $ make_bytes txt]
          in XML.Elem (markup', body)) args)

reportString :: SourcePos -> Markup.T -> String -> IO ()
reportString pos markup txt = reportsString [((pos, markup), txt)]

reports :: [Report] -> IO ()
reports = reportsString . map (, "")

report :: SourcePos -> Markup.T -> IO ()
report pos markup = reports [(pos, markup)]


-- output

trimString :: String -> String
trimString = trim_line

messageBytes :: Maybe PIDE -> Bytes -> Kind -> SourcePos -> Bytes -> [Bytes]
messageBytes pide origin kind pos msg =
  if isJust pide then
    pideMessage $ YXML.string_of $ xmlMessage (fromJust pide) origin kind pos msg
  else
    [(if Bytes.null origin then "" else "[" <> origin <> "] ") <>
      (case show kind of "" -> "" ; s -> make_bytes s <> ": ") <>
      (case show pos of "" -> ""; s -> make_bytes s <> "\n")
    , msg]

output :: Bytes -> Kind -> SourcePos -> Bytes -> IO ()
output origin kind pos msg = do
  context <- getContext
  channel context $ messageBytes (pide context) origin kind pos msg

error :: Bytes -> SourcePos -> Bytes -> IO a
error origin pos msg = do
  pide <- pideContext
  errorWithoutStackTrace $ UTF8.decode $ Bytes.concat $ messageBytes pide origin ERROR pos msg


-- specific messages

outputMain, outputExport, outputForTheL, outputParser, outputReasoner,
  outputSimplifier, outputThesis :: Kind -> SourcePos -> Bytes -> IO ()
outputMain = output Naproche.origin_main
outputExport = output Naproche.origin_export
outputForTheL = output Naproche.origin_forthel
outputParser = output Naproche.origin_parser
outputReasoner = output Naproche.origin_reasoner
outputSimplifier = output Naproche.origin_simplifier
outputThesis = output Naproche.origin_thesis

outputTranslate :: Kind -> SourcePos -> Bytes -> IO ()
outputTranslate = output Naproche.origin_translate

errorExport :: SourcePos -> Bytes -> IO a
errorExport = error Naproche.origin_export

errorParser :: SourcePos -> Bytes -> IO a
errorParser = error Naproche.origin_parser
