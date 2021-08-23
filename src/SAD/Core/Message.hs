{-
Authors: Makarius Wenzel (2018, 2021)

Formal output messages, with PIDE (Prover IDE) support.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}

module SAD.Core.Message (
  Kind (..), entity_markup,
  Report, Report_Text, reports_text, report_text, reports, report,
  console_position, show_position,
  output, Error (..), error,
  outputMain, outputExport, outputForTheL, outputParser, outputReasoner,
  outputThesis, outputSimplifier, outputTranslate,
  errorExport, errorParser
)
where

import Prelude hiding (error)
import Control.Monad
import Data.Maybe (catMaybes, mapMaybe)
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
import qualified Isabelle.Naproche as Naproche
import Isabelle.Library

import qualified Naproche.Program as Program


-- PIDE markup

position_properties_of :: Program.Context -> Position.T -> Properties.T
position_properties_of context =
  Position.properties_of . Program.adjust_position context

entity_markup :: Bytes -> Bytes -> Bool -> Int -> Position.T -> Markup.T
entity_markup kind name def serial pos =
  Markup.entity kind name
  |> Markup.properties (Position.entity_properties_of def serial pos)


-- PIDE markup reports

type Report = (Position.T, Markup.T)
type Report_Text = (Report, Bytes)

reports_text :: [Report_Text] -> IO ()
reports_text args = do
  context <- Program.thread_context
  when (Program.is_pide context && not (null args)) $
    Program.write_message context
      (Naproche.output_report_command :
        map (\((pos, markup), txt) ->
          let
            props = position_properties_of context pos
            markup' = Markup.properties props markup
            body = if Bytes.null txt then [] else [XML.Text txt]
          in YXML.string_of $ XML.Elem (markup', body)) args)

report_text :: Position.T -> Markup.T -> Bytes -> IO ()
report_text pos markup txt = reports_text [((pos, markup), txt)]

reports :: [Report] -> IO ()
reports = reports_text . map (, Bytes.empty)

report :: Position.T -> Markup.T -> IO ()
report pos markup = reports [(pos, markup)]


-- console position

console_position :: Position.T -> Bytes
console_position pos = space_implode " " (catMaybes [file_name, details])
  where
    file_name = quote <$> Position.file_of pos
    details =
      case mapMaybe detail [("line", Position.line_of), ("column", Position.column_of)] of
        [] -> Nothing
        ds -> Just ("(" <> commas ds <> ")")
    detail (a, f) = (\i -> a <> " " <> Value.print_int i) <$> f pos

show_position :: Position.T -> String
show_position = make_string . console_position


-- PIDE output messages

data Kind =
  STATE | WRITELN | INFORMATION | TRACING | WARNING | LEGACY_FEATURE | ERROR

console_kind :: Kind -> Bytes
console_kind WARNING = "Warning"
console_kind LEGACY_FEATURE = "Legacy feature"
console_kind ERROR = "Error"
console_kind _ = ""

pide_kind :: Kind -> Bytes
pide_kind STATE = Naproche.output_state_command
pide_kind WRITELN = Naproche.output_writeln_command
pide_kind INFORMATION = Naproche.output_information_command
pide_kind TRACING = Naproche.output_tracing_command
pide_kind WARNING = Naproche.output_warning_command
pide_kind LEGACY_FEATURE = Naproche.output_legacy_feature_command
pide_kind ERROR = Naproche.output_error_command

message_chunks :: Program.Context -> Kind -> Bytes -> Position.T -> Bytes -> [Bytes]
message_chunks context kind origin pos text =
  if Program.is_pide context then
    let
      command = pide_kind kind
      position = YXML.string_of_body $ Encode.properties $ position_properties_of context pos
    in [command, origin, position, text]
  else
    let
      k = console_kind kind
      p = console_position pos
      chunk =
        (if Bytes.null origin then "" else "[" <> origin <> "] ") <>
        (if Bytes.null k then "" else make_bytes (k <> ": ")) <>
        (if Bytes.null p then "" else make_bytes (p <> "\n")) <> text
    in [chunk]

output :: BYTES a => Bytes -> Kind -> Position.T -> a -> IO ()
output origin kind pos msg = do
  context <- Program.thread_context
  Program.write_message context $ message_chunks context kind origin pos (make_bytes msg)


-- errors

newtype Error = Error [Bytes]
instance Show Error where show (Error chunks) = make_string $ cat_lines chunks
instance Exception Error

error :: BYTES a => Bytes -> Position.T -> a -> IO b
error origin pos msg = do
  context <- Program.thread_context
  let chunks = message_chunks context ERROR origin pos (make_bytes msg)
  if Program.is_pide context then Exception.throw $ Error chunks
  else errorWithoutStackTrace $ make_string $ cat_lines chunks


-- message origins

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

errorExport :: BYTES a => Position.T -> a -> IO b
errorExport = error Naproche.origin_export

errorParser :: BYTES a => Position.T -> a -> IO b
errorParser = error Naproche.origin_parser
