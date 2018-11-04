{-
Authors: Makarius Wenzel (2018)

Formal output messages, with Prover IDE support.
-}

module Alice.Core.Message (Kind (..), checkPIDE,
  output, outputMain, outputExport, outputForTheL,
  outputParser, outputReason, outputThesis, outputSimp,
  trim
)

where

import Alice.Core.Position
import System.Environment
import Isabelle.Library as Isabelle
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.UTF8 as UTF8


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

checkPIDE :: IO Bool
checkPIDE = do
  pide <- lookupEnv "SAD3_PIDE"
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
      putStrLn $ "\001" ++ show (ByteString.length bytes)
      ByteString.putStr bytes
      putStrLn ""
  else putStrLn $ textMessage origin kind pos msg

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
