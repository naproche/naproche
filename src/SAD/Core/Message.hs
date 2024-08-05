-- |
-- Module      : SAD.Core.Message
-- Copyright   : (c) 2018, 2021, Makarius Wenzel
-- License     : GPL-3
--
-- Formal output messages, with PIDE (Prover IDE) support.


{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module SAD.Core.Message (
  reports_text, report_text, reports, report,
  console_position, show_position,
  origin_main, origin_export, origin_forthel, origin_parser,
  origin_reasoner, origin_simplifier, origin_thesis, origin_translate,
  Kind (..), output, error,
  outputMain, outputExport, outputForTheL, outputParser, outputReasoner,
  outputThesis, outputSimplifier, outputTranslate,
  errorExport, errorParser, errorLexer, errorTokenizer
) where

import Prelude hiding (error)
import Control.Monad (when)
import Data.Maybe (catMaybes, mapMaybe)

import Isabelle.Bytes qualified as Bytes
import Isabelle.Bytes (Bytes)
import Isabelle.Position qualified as Position
import Isabelle.Value qualified as Value
import Isabelle.Markup qualified as Markup
import Isabelle.XML qualified as XML
import Isabelle.YXML qualified as YXML
import Isabelle.Naproche qualified as Naproche
import Isabelle.Library

import Naproche.Program qualified as Program


-- PIDE markup reports

reports_text :: [Position.Report_Text] -> IO ()
reports_text args = do
  context <- Program.thread_context
  when (Program.is_pide context && not (null args)) $
    Program.exchange_message0 context
      (Naproche.output_report_command :
        map (\((pos, markup), txt) ->
          let
            pos' = Program.adjust_position context pos
            markup' = Markup.properties (Position.properties_of pos') markup
            body = if Bytes.null txt then [] else [XML.Text txt]
          in YXML.string_of $ XML.Elem (markup', body)) args)

report_text :: Position.T -> Markup.T -> Bytes -> IO ()
report_text pos markup txt = reports_text [((pos, markup), txt)]

reports :: [Position.Report] -> IO ()
reports = reports_text . map (, Bytes.empty)

report :: Position.T -> Markup.T -> IO ()
report pos markup = reports [(pos, markup)]


-- message origin

origin_main, origin_export, origin_forthel, origin_parser,
  origin_reasoner, origin_simplifier, origin_thesis, origin_translate,
  origin_lexer, origin_tokenizer :: Bytes
origin_main = "Main"
origin_export = "Export"
origin_forthel = "ForTheL"
origin_parser = "Parser"
origin_reasoner = "Reasoner"
origin_simplifier = "Simplifier"
origin_thesis = "Thesis"
origin_translate = "Translation"
origin_lexer = "Lexer"
origin_tokenizer = "Tokenizer"


-- message kind

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


-- make formal message

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

make_message :: Program.Context -> Kind -> Bytes -> Position.T -> Bytes -> (Bytes, Bytes)
make_message context kind origin pos text =
  if Program.is_pide context then
    let
      k = pide_kind kind
      p = Position.here (Program.adjust_position context pos)
      msg =
        enclose "[" "]" (if Bytes.null origin then origin_main else origin) <>
        (if Bytes.null p then " " else p <> "\n") <> text
    in (k, msg)
  else
    let
      k = console_kind kind
      p = console_position pos
      msg =
        (if Bytes.null origin then "" else "[" <> origin <> "] ") <>
        (if Bytes.null k then "" else k <> ": ") <>
        (if Bytes.null p then "" else p <> "\n") <> text
    in ("", msg)

output :: BYTES a => Bytes -> Kind -> Position.T -> a -> IO ()
output origin kind pos text = do
  context <- Program.thread_context
  let (command, msg) = make_message context kind origin pos (make_bytes text)
  Program.exchange_message0 context [command, msg]

error :: BYTES a => Bytes -> Position.T -> a -> IO b
error origin pos text = do
  context <- Program.thread_context
  Program.error $ snd $ make_message context ERROR origin pos (make_bytes text)


-- common messages

outputMain, outputExport, outputForTheL, outputParser, outputReasoner,
  outputSimplifier, outputThesis :: BYTES a => Kind -> Position.T -> a -> IO ()
outputMain = output origin_main
outputExport = output origin_export
outputForTheL = output origin_forthel
outputParser = output origin_parser
outputReasoner = output origin_reasoner
outputSimplifier = output origin_simplifier
outputThesis = output origin_thesis

outputTranslate :: BYTES a => Kind -> Position.T -> a -> IO ()
outputTranslate = output origin_translate

errorExport, errorParser, errorLexer, errorTokenizer :: BYTES a => Position.T -> a -> IO b
errorExport = error origin_export
errorParser = error origin_parser
errorLexer = error origin_lexer
errorTokenizer = error origin_tokenizer
