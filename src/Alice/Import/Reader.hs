{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Main text reading functions.
-}

module Alice.Import.Reader (readInit, readText) where

import Data.List
import Control.Monad
import System.IO
import System.IO.Error
import Control.Exception

import Alice.Data.Text.Block
import Alice.Data.Instr
import Alice.ForTheL.Base
import Alice.ForTheL.Structure
import Alice.Parser.Base
import Alice.ForTheL.Instruction
import Alice.Core.Position
import Alice.Parser.Token
import Alice.Parser.Combinators
import Alice.Parser.Primitives
import Alice.Parser.Error
import qualified Alice.Core.Message as Message
import qualified Isabelle.File as File


-- Init file parsing

readInit :: String -> IO [Instr]
readInit "" = return []
readInit file = do
  input <- catch (File.read file) $ Message.errorParser (fileOnlyPos file) . ioeGetErrorString
  let tokens = filter properToken $ tokenize (filePos file) input
      initialParserState = State () tokens noPos
  fst <$> launchParser instructionFile initialParserState

instructionFile :: Parser st [Instr]
instructionFile = after (optLL1 [] $ chainLL1 instr) eof


-- Reader loop

readText :: String -> [Text] -> IO [Text]
readText pathToLibrary text0 = do
  text <- reader pathToLibrary [] [State initFS noTokens noPos] text0
  pide <- Message.pideActive
  when pide $ Message.reports $ concatMap textReports text
  return text

reader :: String -> [String] -> [State FState] -> [Text] -> IO [Text]

reader _ _ _ [TI (InStr ISread file)] | isInfixOf ".." file =
  Message.errorParser (fileOnlyPos file) "contains \"..\", not allowed"

reader pathToLibrary doneFiles stateList [TI (InStr ISread file)] =
  reader pathToLibrary doneFiles stateList
    [TI $ InStr ISfile $ pathToLibrary ++ '/' : file]

reader pathToLibrary doneFiles (pState:states) [TI (InStr ISfile file)]
  | file `elem` doneFiles = do
      Message.outputMain Message.WRITELN (fileOnlyPos file) "already read, skipping"
      (newText, newState) <- launchParser forthel pState
      reader pathToLibrary doneFiles (newState:states) newText

reader pathToLibrary doneFiles (pState:states) [TI (InStr ISfile file)] = do
  input <-
    catch (if null file then getContents else File.read file)
      (Message.errorParser (fileOnlyPos file) . ioeGetErrorString)
  let tokens0 = tokenize (filePos file) input
  Message.reports $ concatMap tokenReports tokens0
  let tokens = filter properToken tokens0
      st  = State ((stUser pState) { tvr_expr = [] }) tokens noPos
  (ntx, nps) <- launchParser forthel st
  reader pathToLibrary (file:doneFiles) (nps:pState:states) ntx

-- this happens when t is not a suitable instruction
reader pathToLibrary doneFiles stateList (t:restText) =
  (t:) <$> reader pathToLibrary doneFiles stateList restText

reader pathToLibrary doneFiles (pState:oldState:rest) [] = do
  Message.outputParser Message.WRITELN (fileOnlyPos $ head doneFiles) "parsing successful"
  let resetState = oldState {
        stUser = (stUser pState) {tvr_expr = tvr_expr $ stUser oldState}}
  (newText, newState) <- launchParser forthel resetState
  reader pathToLibrary doneFiles (newState:rest) newText

reader _ _ _ [] = return []



-- launch a parser in the IO monad
launchParser :: Parser st a -> State st -> IO (a, State st)
launchParser parser state =
  case runP parser state of
    Error err -> Message.errorParser (errorPos err) (show err)
    Ok [PR a st] -> return (a, st)
