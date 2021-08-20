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
  Kind (..), entityMarkup, is_pide_message,
  Report, ReportString, reportsString, reportString, reports, report,
  trimString, messageBytes, output, error, outputMain, outputExport, outputForTheL,
  outputParser, outputReasoner, outputThesis, outputSimplifier, outputTranslate,
  errorExport, errorParser
) where

import Prelude hiding (error)
import Control.Monad
import Data.Maybe
import Data.IORef
import System.IO.Unsafe
import Data.Map.Strict (Map)
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
import qualified Isabelle.XML as XML
import qualified Isabelle.XML.Encode as Encode
import qualified Isabelle.YXML as YXML
import qualified Isabelle.Options as Options
import qualified Isabelle.Naproche as Naproche
import Isabelle.Library (BYTES, make_string, make_bytes, trim_line, space_implode)


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

initThread :: Options.T -> Channel -> IO ()
initThread options channel =
  updateState (\id -> Map.insert id (Context (Just $ PIDE pide file shift) channel))
  where
    pide = Options.string options Naproche.naproche_pos_id
    file = Options.string options Naproche.naproche_pos_file
    shift = Options.int options Naproche.naproche_pos_shift

exitThread :: IO ()
exitThread = updateState Map.delete

consoleThread :: IO ()
consoleThread = updateState (\id -> Map.insert id defaultContext)


-- PIDE messages

data Kind =
  STATE | WRITELN | INFORMATION | TRACING | WARNING | LEGACY | ERROR

instance Show Kind where
  show WARNING = "Warning"
  show LEGACY = "Legacy feature"
  show ERROR = "Error"
  show _ = ""

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

pide_message :: PIDE -> Bytes -> Kind -> SourcePos -> Bytes -> [Bytes]
pide_message pide origin kind pos msg = [kind_name, origin, position, msg]
  where
    kind_name =
      case kind of
        STATE -> Markup.stateN
        WRITELN -> Markup.writelnN
        INFORMATION -> Markup.informationN
        TRACING -> Markup.tracingN
        WARNING -> Markup.warningN
        LEGACY -> Markup.legacyN
        ERROR -> Markup.errorN
    position = YXML.string_of_body $ Encode.properties $ posProperties pide pos

is_pide_message :: [Bytes] -> Bool
is_pide_message chunks = length chunks == 4


-- PIDE markup reports

type Report = (SourcePos, Markup.T)
type ReportString = (Report, String)

reportsString :: [ReportString] -> IO ()
reportsString args = do
  context <- getContext
  when (isJust (pide context) && not (null args)) $
    channel context (Markup.reportN :
        map (\((pos, markup), txt) ->
          let
            markup' = Markup.properties (posProperties (fromJust (pide context)) pos) markup
            body = if null txt then [] else [XML.Text $ make_bytes txt]
          in YXML.string_of $ XML.Elem (markup', body)) args)

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
messageBytes (Just pide) origin kind pos msg = pide_message pide origin kind pos msg
messageBytes Nothing origin kind pos msg =
  [(if Bytes.null origin then "" else "[" <> origin <> "] ") <>
   (case show kind of "" -> "" ; s -> make_bytes s <> ": ") <>
   (case show pos of "" -> ""; s -> make_bytes s <> "\n") <> msg]

output :: BYTES a => Bytes -> Kind -> SourcePos -> a -> IO ()
output origin kind pos msg = do
  context <- getContext
  channel context $ messageBytes (pide context) origin kind pos (make_bytes msg)

error :: BYTES a => Bytes -> SourcePos -> a -> IO b
error origin pos msg = do
  pide <- pideContext
  errorWithoutStackTrace $ make_string $
    space_implode (Bytes.singleton 0) $
    messageBytes pide origin ERROR pos (make_bytes msg)


-- specific messages

outputMain, outputExport, outputForTheL, outputParser, outputReasoner,
  outputSimplifier, outputThesis :: BYTES a => Kind -> SourcePos -> a -> IO ()
outputMain = output Naproche.origin_main
outputExport = output Naproche.origin_export
outputForTheL = output Naproche.origin_forthel
outputParser = output Naproche.origin_parser
outputReasoner = output Naproche.origin_reasoner
outputSimplifier = output Naproche.origin_simplifier
outputThesis = output Naproche.origin_thesis

outputTranslate :: BYTES a => Kind -> SourcePos -> a -> IO ()
outputTranslate = output Naproche.origin_translate

errorExport :: BYTES a => SourcePos -> a -> IO b
errorExport = error Naproche.origin_export

errorParser :: BYTES a => SourcePos -> a -> IO b
errorParser = error Naproche.origin_parser
