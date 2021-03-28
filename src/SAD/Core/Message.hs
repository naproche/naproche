{-
Authors: Makarius Wenzel (2018)

Formal output messages, with PIDE (Prover IDE) support.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}

module SAD.Core.Message (
  PIDE(..), Kind (..), entityMarkup, posProperties,
  Report, ReportString, reportString, reportMeta, report,
  trimString, Comm(..), outputMain, outputExport, outputForTheL,
  outputParser, outputReasoner, outputThesis, outputSimplifier, outputTranslate,
  errorExport, errorParser
) where

import Prelude hiding (error)

import SAD.Core.SourcePos (SourcePos)
import qualified SAD.Core.SourcePos as SourcePos

import qualified Isabelle.Value as Value
import qualified Isabelle.Markup as Markup
import qualified Isabelle.Naproche as Naproche
import qualified Isabelle.Library as Library

data PIDE = PIDE {pideID :: String, pideFile :: String, pideShift :: Int}

data Kind =
  STATE | WRITELN | INFORMATION | TRACING | WARNING | LEGACY | ERROR

instance Show Kind where
  show WARNING = "Warning"
  show LEGACY = "Legacy feature"
  show ERROR = "Error"
  show _ = ""

class Monad m => Comm m where
  output :: String -> Kind -> SourcePos -> String -> m ()
  error :: String -> SourcePos -> String -> m a
  reportsString :: [ReportString] -> m ()
  pideContext :: m (Maybe PIDE)
  textFieldWidth :: m Int

type Report = (SourcePos, Markup.T)
type ReportString = (Report, String)

reportString :: Comm m => SourcePos -> Markup.T -> String -> m ()
reportString pos markup txt = reportsString [((pos, markup), txt)]

reportMeta :: Comm m => [Report] -> m ()
reportMeta = reportsString . map (, "")

report :: Comm m => SourcePos -> Markup.T -> m ()
report pos markup = reportMeta [(pos, markup)]


-- output

trimString :: String -> String
trimString = Library.trim_line

posProperties :: PIDE -> SourcePos -> [(String, String)]
posProperties PIDE{pideID, pideFile, pideShift} pos =
  (if null pideID then [] else [(Markup.idN, pideID)]) ++
  (if null file then [] else [(Markup.fileN, file)]) ++
  (if line <= 0 then [] else [(Markup.lineN, Value.print_int line)]) ++
  (if offset <= 0 then [] else [(Markup.offsetN, Value.print_int offset)]) ++
  (if endOffset <= 0 then [] else [(Markup.end_offsetN, Value.print_int endOffset)])
  where
    file = if null $ SourcePos.sourceFile pos then pideFile else SourcePos.sourceFile pos
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


-- specific messages

outputMain, outputExport, outputForTheL, outputParser, outputReasoner,
  outputSimplifier, outputThesis :: Comm m => Kind -> SourcePos -> String -> m ()
outputMain = output Naproche.origin_main
outputExport = output Naproche.origin_export
outputForTheL = output Naproche.origin_forthel
outputParser = output Naproche.origin_parser
outputReasoner = output Naproche.origin_reasoner
outputSimplifier = output Naproche.origin_simplifier
outputThesis = output Naproche.origin_thesis

outputTranslate :: Comm m => Kind -> SourcePos -> String -> m ()
outputTranslate = output Naproche.origin_translate

errorExport :: Comm m => SourcePos -> String -> m a
errorExport = error Naproche.origin_export

errorParser :: Comm m => SourcePos -> String -> m a
errorParser = error Naproche.origin_parser
