{-
Authors: Makarius Wenzel (2018, 2021)

Formal output messages, with PIDE (Prover IDE) support.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}

module SAD.Core.Message (
  PIDE, pideContext, pideActive,
  initThread, exitThread, consoleThread,
  Kind (..), entity_markup,
  Report, Report_Text, reports_text, report_text, reports, report,
  print_position, show_position,
  output, outputMain, outputExport, outputForTheL,
  outputParser, outputReasoner, outputThesis, outputSimplifier, outputTranslate,
  Error (..), error, errorExport, errorParser
) where

import Prelude hiding (error)
import Control.Monad
import Data.Maybe (isJust, fromJust, fromMaybe, mapMaybe, catMaybes)
import Data.IORef
import System.IO.Unsafe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.ByteString.Char8 as Char8
import Control.Concurrent (ThreadId)
import qualified Control.Concurrent as Concurrent

import qualified Control.Exception as Exception
import Control.Exception (Exception)
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Position as Position
import qualified Isabelle.Value as Value
import qualified Isabelle.Markup as Markup
import qualified Isabelle.XML as XML
import qualified Isabelle.XML.Encode as Encode
import qualified Isabelle.YXML as YXML
import qualified Isabelle.Options as Options
import qualified Isabelle.Naproche as Naproche
import Isabelle.Library


-- PIDE thread context

data PIDE = PIDE { _id :: Bytes, _file :: Bytes, _shift :: Int }
type Channel = [Bytes] -> IO ()
data Context = Context { _pide :: Maybe PIDE, _channel :: Channel }

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
pideContext = _pide <$> getContext

pideActive :: IO Bool
pideActive = isJust <$> pideContext


-- init/exit thread context

initThread :: Options.T -> Channel -> IO ()
initThread options channel =
  updateState (\id -> Map.insert id (Context (Just pide) channel))
  where
    pide =
      PIDE {
        _id = Options.string options Naproche.naproche_pos_id,
        _file = Options.string options Naproche.naproche_pos_file,
        _shift = Options.int options Naproche.naproche_pos_shift
      }

exitThread :: IO ()
exitThread = updateState Map.delete

consoleThread :: IO ()
consoleThread = updateState (\id -> Map.insert id defaultContext)


-- PIDE markup

pide_position :: PIDE -> Position.T -> Position.T
pide_position pide pos =
  pos
  |> Position.put_file (fromMaybe (_file pide) (Position.file_of pos))
  |> Position.put_id (_id pide)
  |> Position.shift_offsets (_shift pide)

position_properties_of :: PIDE -> Position.T -> Properties.T
position_properties_of pide = Position.properties_of . pide_position pide

entity_markup :: PIDE -> Bytes -> Bytes -> Bool -> Int -> Position.T -> Markup.T
entity_markup pide kind name def serial pos =
  Markup.entity kind name
  |> Markup.properties (Position.entity_properties_of def serial pos)


-- PIDE markup reports

type Report = (Position.T, Markup.T)
type Report_Text = (Report, Bytes)

reports_text :: [Report_Text] -> IO ()
reports_text args = do
  context <- getContext
  when (isJust (_pide context) && not (null args)) $
    _channel context (Naproche.output_report_command :
        map (\((pos, markup), txt) ->
          let
            props = position_properties_of (fromJust (_pide context)) pos
            markup' = Markup.properties props markup
            body = if Bytes.null txt then [] else [XML.Text txt]
          in YXML.string_of $ XML.Elem (markup', body)) args)

report_text :: Position.T -> Markup.T -> Bytes -> IO ()
report_text pos markup txt = reports_text [((pos, markup), txt)]

reports :: [Report] -> IO ()
reports = reports_text . map (, Bytes.empty)

report :: Position.T -> Markup.T -> IO ()
report pos markup = reports [(pos, markup)]


-- PIDE output messages

data Kind =
  STATE | WRITELN | INFORMATION | TRACING | WARNING | LEGACY_FEATURE | ERROR

print_position :: Position.T -> Bytes
print_position pos = space_implode " " (catMaybes [file_name, details])
  where
    file_name = quote <$> Position.file_of pos
    details =
      case mapMaybe detail [("line", Position.line_of), ("column", Position.column_of)] of
        [] -> Nothing
        ds -> Just ("(" <> commas ds <> ")")
    detail (a, f) = (\i -> a <> " " <> Value.print_int i) <$> f pos

show_position :: Position.T -> String
show_position = make_string . print_position

message_chunks :: Maybe PIDE -> Kind -> Bytes -> Position.T -> Bytes -> [Bytes]
message_chunks (Just pide) kind origin pos text = [command, origin, position, text]
  where
    command =
      case kind of
        STATE -> Naproche.output_state_command
        WRITELN -> Naproche.output_writeln_command
        INFORMATION -> Naproche.output_information_command
        TRACING -> Naproche.output_tracing_command
        WARNING -> Naproche.output_warning_command
        LEGACY_FEATURE -> Naproche.output_legacy_feature_command
        ERROR -> Naproche.output_error_command
    position = YXML.string_of_body $ Encode.properties $ position_properties_of pide pos
message_chunks Nothing kind origin pos text = [chunk]
  where
    chunk =
      (if Bytes.null origin then "" else "[" <> origin <> "] ") <>
      (if Bytes.null print_kind then "" else make_bytes (print_kind <> ": ")) <>
      (if Bytes.null print_pos then "" else make_bytes (print_pos <> "\n")) <> text
    print_kind =
      case kind of
        WARNING -> "Warning"
        LEGACY_FEATURE -> "Legacy feature"
        ERROR -> "Error"
        _ -> ""
    print_pos = print_position pos

output :: BYTES a => Bytes -> Kind -> Position.T -> a -> IO ()
output origin kind pos msg = do
  context <- getContext
  _channel context $ message_chunks (_pide context) kind origin pos (make_bytes msg)

outputMain, outputExport, outputForTheL, outputParser, outputReasoner,
  outputSimplifier, outputThesis :: BYTES a => Kind -> Position.T -> a -> IO ()
outputMain = output Naproche.origin_main
outputExport = output Naproche.origin_export
outputForTheL = output Naproche.origin_forthel
outputParser = output Naproche.origin_parser
outputReasoner = output Naproche.origin_reasoner
outputSimplifier = output Naproche.origin_simplifier
outputThesis = output Naproche.origin_thesis

outputTranslate :: BYTES a => Kind -> Position.T -> a -> IO ()
outputTranslate = output Naproche.origin_translate


-- errors

newtype Error = Error [Bytes]
instance Show Error where show (Error chunks) = make_string $ cat_lines chunks
instance Exception Error

error :: BYTES a => Bytes -> Position.T -> a -> IO b
error origin pos msg = do
  pide <- pideContext
  let chunks = message_chunks pide ERROR origin pos (make_bytes msg)
  if isJust pide then Exception.throw $ Error chunks
  else errorWithoutStackTrace $ make_string $ cat_lines chunks

errorExport :: BYTES a => Position.T -> a -> IO b
errorExport = error Naproche.origin_export

errorParser :: BYTES a => Position.T -> a -> IO b
errorParser = error Naproche.origin_parser
