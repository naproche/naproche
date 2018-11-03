{-
Authors: Makarius Wenzel (2018)

Formal output messages, with Prover IDE support.
-}

module Alice.Core.Message (
  trimLine, Kind (..),
  outputMessage, outputMain, outputExport, outputForTheL,
  outputParser, outputReason, outputThesis, outputSimp
)

where

import Alice.Core.Position
import System.Environment
import Isabelle.Library as Isabelle
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.UTF8 as UTF8


trimLine :: String -> String
trimLine = Isabelle.trim_line

data Kind = NORMAL | WARNING | ERROR
instance Show Kind where
  show NORMAL = ""
  show WARNING = "Warning"
  show ERROR = "Error"

xmlKind :: Kind -> String
xmlKind NORMAL = "writeln"
xmlKind WARNING = "warning"
xmlKind ERROR = "error"

xmlMessage :: String -> Kind -> SourcePos -> String -> XML.Tree
xmlMessage origin kind pos msg =
  XML.Elem (xmlKind kind, props) [XML.Text msg]
  where
    props =
      if null origin then posProperties pos
      else ("origin", origin) : posProperties pos

textMessage :: String -> Kind -> SourcePos -> String -> String
textMessage origin kind pos msg =
  (if null origin then "" else "[" ++ origin ++ "] ") ++
  (case show kind of "" -> "" ; s -> s ++ ": ") ++
  (case show pos of "" -> ""; s -> s ++ "\n") ++ msg

outputMessage :: String -> Kind -> SourcePos -> String -> IO ()
outputMessage origin kind pos msg = do
  pide <- lookupEnv "SAD3_PIDE"
  case pide of
    Just "true" ->
      let
        string = YXML.string_of (xmlMessage origin kind pos msg)
        bytes = UTF8.fromString string
      in do
        putStrLn $ "\001" ++ show (ByteString.length bytes)
        ByteString.putStr bytes
        putStrLn ""
    _ -> putStrLn $ textMessage origin kind pos msg

outputMain :: Kind -> SourcePos -> String -> IO ()
outputMain = outputMessage "Main"

outputExport :: Kind -> SourcePos -> String -> IO ()
outputExport = outputMessage "Export"

outputForTheL :: Kind -> SourcePos -> String -> IO ()
outputForTheL = outputMessage "ForTheL"

outputParser :: Kind -> SourcePos -> String -> IO ()
outputParser = outputMessage "Parser"

outputReason :: Kind -> SourcePos -> String -> IO ()
outputReason = outputMessage "Reasoner"

outputThesis :: Kind -> SourcePos -> Int -> String -> IO ()
outputThesis kind pos indent msg =
  outputMessage "Thesis" kind pos $ replicate (3 * indent) ' ' ++ msg

outputSimp :: Kind -> SourcePos -> String -> IO ()
outputSimp = outputMessage "Simplifier"
