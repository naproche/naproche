{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Main text reading functions.
-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Import.Reader (readInit, readProofText) where

import Data.Maybe
import Control.Monad
import System.IO.Error
import Control.Exception
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

import SAD.Data.Text.Block
import SAD.Data.Instr as Instr
import SAD.ForTheL.Base
import SAD.ForTheL.Structure
import SAD.Parser.Base
import SAD.ForTheL.Instruction
import SAD.Core.SourcePos
import SAD.Parser.Token
import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.Parser.Error
import qualified SAD.Core.Message as Message
import qualified Isabelle.File as File

-- Init file parsing

readInit :: Text -> IO [(Pos, Instr)]
readInit "" = return []
readInit file = do
  input <- catch (File.read (Text.unpack file)) $ Message.errorParser (fileOnlyPos file) . ioeGetErrorString
  let tokens = filter isProperToken $ tokenize (filePos file) $ Text.pack input
      initialParserState = State (initFS Nothing) tokens noSourcePos
  fst <$> launchParser instructionFile initialParserState

instructionFile :: FTL [(Pos, Instr)]
instructionFile = after (optLL1 [] $ chainLL1 instr) eof


-- Reader loop

readProofText :: Text -> [ProofText] -> IO [ProofText]
readProofText pathToLibrary text0 = do
  pide <- Message.pideContext
  (text, reports) <- reader pathToLibrary [] [State (initFS pide) noTokens noSourcePos] text0
  when (isJust pide) $ Message.reports reports
  return text

reader :: Text -> [Text] -> [State FState] -> [ProofText] -> IO ([ProofText], [Message.Report])
reader pathToLibrary doneFiles = go
  where
    go stateList [ProofTextInstr pos (GetArgument Read file)] = if ".." `Text.isInfixOf` file
      then Message.errorParser (Instr.position pos) ("Illegal \"..\" in file name: " ++ show file)
      else go stateList [ProofTextInstr pos $ GetArgument File $ pathToLibrary <> "/" <> file]

    go (pState:states) [ProofTextInstr pos (GetArgument File file)]
      | file `elem` doneFiles = do
          Message.outputMain Message.WARNING (Instr.position pos)
            ("Skipping already read file: " ++ show file)
          (newProofText, newState) <- launchParser forthel pState
          go (newState:states) newProofText

    go (pState:states) [ProofTextInstr _ (GetArgument File file)] = do
      text <-
        catch (if Text.null file then getContents else File.read $ Text.unpack file)
          (Message.errorParser (fileOnlyPos file) . ioeGetErrorString)
      (newProofText, newState) <- reader0 (filePos file) (Text.pack text) pState
      reader pathToLibrary (file:doneFiles) (newState:pState:states) newProofText

    go (pState:states) [ProofTextInstr _ (GetArgument Text text)] = do
      (newProofText, newState) <- reader0 startPos text pState
      go (newState:pState:states) newProofText

    -- this happens when t is not a suitable instruction
    -- e.g. all the time, since we feed every parsed ProofText through this loop
    go stateList (t:restProofText) = do
      (ts, ls) <- go stateList restProofText
      return (t:ts, ls)

    go (pState:oldState:rest) [] = do
      Message.outputParser Message.TRACING
        (if null doneFiles then noSourcePos else fileOnlyPos $ head doneFiles) "parsing successful"
      let resetState = oldState {
            stUser = (stUser pState) {tvrExpr = tvrExpr $ stUser oldState}}
      (newProofText, newState) <- launchParser forthel resetState
      go (newState:rest) newProofText

    go (state:_) [] = return ([], reports $ stUser state)

reader0 :: SourcePos -> Text -> State FState -> IO ([ProofText], State FState)
reader0 pos text pState = do
  let tokens0 = tokenize pos text
  Message.reports $ concatMap (maybeToList . reportComments) tokens0
  let tokens = filter isProperToken tokens0
      st = State ((stUser pState) { tvrExpr = [] }) tokens noSourcePos
  launchParser forthel st


-- launch a parser in the IO monad
launchParser :: Parser st a -> State st -> IO (a, State st)
launchParser parser state =
  case runP parser state of
    Error err -> Message.errorParser (errorPos err) (show err)
    Ok [PR a st] -> return (a, st)
