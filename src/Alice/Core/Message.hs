{-
Authors: Makarius Wenzel (2018)

Formal output messages, with Prover IDE support.
-}

module Alice.Core.Message (Kind (..), checkPIDE,
  output, outputMain, outputExport, outputForTheL,
  outputParser, outputReason, outputThesis, outputSimp,
  trim
) where

import System.Environment
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.UTF8 as UTF8

import Alice.Core.Position (SourcePos)
import qualified Alice.Core.Position as Position

import Isabelle.Library as Isabelle
import qualified Isabelle.Value as Value
import qualified Isabelle.Markup as Markup
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML


{- message kind -}

data Kind =
  STATE | WRITELN | INFORMATION | TRACING | WARNING | LEGACY | ERROR

instance Show Kind where
  show STATE = "State"
  show WRITELN = ""
  show INFORMATION = "Information"
  show TRACING = "Tracing"
  show WARNING = "Warning"
  show LEGACY = "Legacy feature"
  show ERROR = "Error"


{- output as PIDE message -}

kindXML :: Kind -> String
kindXML STATE = Markup.stateN
kindXML WRITELN = Markup.writelnN
kindXML INFORMATION = Markup.informationN
kindXML TRACING = Markup.tracingN
kindXML WARNING = Markup.warningN
kindXML LEGACY = Markup.legacyN
kindXML ERROR = Markup.errorN

posProperties :: SourcePos -> [(String, String)]
posProperties pos =
  (if null file then [] else [(Markup.fileN, file)]) ++
  (if line <= 0 then [] else [(Markup.lineN, Value.print_int line)]) ++
  (if offset <= 0 then [] else [(Markup.offsetN, Value.print_int offset)]) ++
  (if endOffset <= 0 then [] else [(Markup.end_offsetN, Value.print_int endOffset)])
  where
    file = Position.sourceFile pos
    line = Position.sourceLine pos
    offset = Position.sourceOffset pos
    endOffset = Position.sourceEndOffset pos

xmlMessage :: String -> Kind -> SourcePos -> String -> XML.Tree
xmlMessage origin kind pos msg =
  XML.Elem (kindXML kind, props) [XML.Text msg]
  where
    props =
      if null origin then posProperties pos
      else ("origin", origin) : posProperties pos


{- output as plain text -}

textMessage :: String -> Kind -> SourcePos -> String -> String
textMessage origin kind pos msg =
  (if null origin then "" else "[" ++ origin ++ "] ") ++
  (case show kind of "" -> "" ; s -> s ++ ": ") ++
  (case show pos of "" -> ""; s -> s ++ "\n") ++ msg


{- conditional output -}

checkPIDE :: IO Bool
checkPIDE = do
  pide <- lookupEnv "NAPROCHE_PIDE"
  case pide of
    Just "true" -> return True
    _ -> return False

output :: String -> Kind -> SourcePos -> String -> IO ()
output origin kind pos msg = do
  pide <- checkPIDE
  if pide then
    let
      string = YXML.string_of (xmlMessage origin kind pos msg)
      bytes = UTF8.fromString string
    in do
      putStrLn $ "\1" ++ Value.print_int (ByteString.length bytes)
      ByteString.putStr bytes
      putStrLn ""
  else putStrLn $ textMessage origin kind pos msg


{- specific messages -}

outputMain, outputExport, outputForTheL, outputParser, outputReason, outputSimp
  :: Kind -> SourcePos -> String -> IO ()
outputMain = output "Main"
outputExport = output "Export"
outputForTheL = output "ForTheL"
outputParser = output "Parser"
outputReason = output "Reasoner"
outputSimp = output "Simplifier"

outputThesis :: Kind -> SourcePos -> Int -> String -> IO ()
outputThesis kind pos indent msg =
  output "Thesis" kind pos $ replicate (3 * indent) ' ' ++ msg

trim :: String -> String
trim = Isabelle.trim_line
