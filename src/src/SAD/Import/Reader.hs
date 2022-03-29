{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Main text reading functions.
-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module SAD.Import.Reader (readInit, readProofText) where

import Data.Maybe
import Control.Monad
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

import SAD.Data.Text.Block
import SAD.Data.Instr as Instr
    ( Argument(Text, File, Read),
      ParserKind(Tex, NonTex),
      Instr(GetArgument))
import SAD.ForTheL.Base
import SAD.ForTheL.Structure
import SAD.Parser.Base
import SAD.ForTheL.Instruction
import SAD.Parser.Token
import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.Parser.Error
import qualified SAD.Core.Message as Message

import qualified Naproche.File as File
import Isabelle.Library (make_bytes, make_string, make_text, show_bytes)
import Isabelle.Position as Position
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Bytes as Bytes

import qualified Naproche.Program as Program
import Control.Monad.IO.Class (MonadIO(liftIO))


-- Init file parsing

readInit :: File.MonadFile m => Bytes -> m [(Position.T, Instr)]
readInit file | Bytes.null file = return []
readInit file = do
  input <- File.read (make_string file)
  let tokens = filter isProperToken $ tokenize TexDisabled (Position.file $ make_bytes file) $ Text.fromStrict $ make_text input
  fst <$> liftIO (launchParser instructionFile (initState Program.Console tokens))

instructionFile :: FTL [(Position.T, Instr)]
instructionFile = after (optLL1 [] $ chainLL1 instr) eof

initState :: Program.MessageExchangeContext c => c -> [Token] -> State FState
initState context tokens = State (initFState context) tokens NonTex Position.none


-- Reader loop

-- | @readProofText startWithTex pathToLibrary text0@ takes:
-- @startWithTex@, a boolean indicating whether to execute the next file instruction using the tex parser,
-- @pathToLibrary@, a path to where the read instruction should look for files and
-- @text0@, containing some configuration.
readProofText :: File.MonadFile m => Bytes -> [ProofText] -> m [ProofText]
readProofText pathToLibrary text0 = do
  context <- liftIO $ Program.thread_context
  (text, reports) <- reader pathToLibrary [] [initState context noTokens] text0
  when (Program.is_pide context) $ liftIO $ Message.reports reports
  return text

reader :: File.MonadFile m => Bytes -> [Text] -> [State FState] -> [ProofText] -> m ([ProofText], [Position.Report])
reader pathToLibrary doneFiles = go
  where
    go stateList [ProofTextInstr pos (GetArgument (Read pk) file)] = if Text.pack ".." `Text.isInfixOf` file
      then liftIO $ Message.errorParser pos ("Illegal \"..\" in file name: " ++ show file)
      else go stateList [ProofTextInstr pos $ GetArgument (File pk) $
            Text.pack (make_string pathToLibrary) <> Text.pack "/" <> file]

    go (pState:states) [ProofTextInstr pos (GetArgument (File parserKind') file)]
      | file `elem` doneFiles = do
          -- The parserKind of the state of the parser indicates whether the file was originally read with the .tex
          -- or the .ftl parser. Now if, for example, we originally read the file with the .ftl format and now we
          -- are reading the file again with the .tex format(by eg using '[readtex myfile.ftl]'), we want to throw an error.
          when (parserKind pState /= parserKind')
            (liftIO $ Message.errorParser pos "Trying to read the same file once in Tex format and once in NonTex format.")
          liftIO $ Message.outputMain Message.WARNING pos
            (make_bytes ("Skipping already read file: " ++ show file))
          (newProofText, newState) <- liftIO $ chooseParser pState
          go (newState:states) newProofText
      | otherwise = do
          text <- if Text.null file then liftIO getContents else make_string <$> File.read (Text.unpack file)
          (newProofText, newState) <- liftIO $ reader0 (Position.file $ make_bytes file) (Text.pack text) (pState {parserKind = parserKind'})
          -- state from before reading is still here
          reader pathToLibrary (file:doneFiles) (newState:pState:states) newProofText

    go (pState:states) [ProofTextInstr _ (GetArgument (Text pk) text)] = do
      (newProofText, newState) <- liftIO $ reader0 Position.start text (pState {parserKind = pk})
      go (newState:pState:states) newProofText -- state from before reading is still here

    -- This says that we are only really processing the last instruction in a [ProofText].
    go stateList (t:restProofText) = do
      (ts, ls) <- go stateList restProofText
      return (t:ts, ls)

    go (pState:oldState:rest) [] = do
      liftIO $ Message.outputParser Message.TRACING
        (if null doneFiles then Position.none else Position.file_only $ make_bytes $ head doneFiles) "parsing successful"
      let resetState = oldState {
            stUser = (stUser pState) {tvrExpr = tvrExpr $ stUser oldState}}
      -- Continue running a parser after eg. a read instruction was evaluated.
      (newProofText, newState) <- liftIO $ chooseParser resetState
      go (newState:rest) newProofText

    go (state:_) [] = return ([], reports $ stUser state)

reader0 :: Position.T -> Text -> State FState -> IO ([ProofText], State FState)
reader0 pos text pState = do
  let tokens0 = chooseTokenizer pState pos text
  Message.reports $ mapMaybe reportComments tokens0
  let tokens = filter isProperToken tokens0
      st = State ((stUser pState) { tvrExpr = [] }) tokens (parserKind pState) Position.none
  chooseParser st


chooseParser :: State FState -> IO ([ProofText], State FState)
chooseParser st = case parserKind st of
  Tex -> launchParser texForthel st
  NonTex -> launchParser forthel st

chooseTokenizer :: State FState -> Position.T -> Text -> [Token]
chooseTokenizer st = case parserKind st of
  Tex -> tokenize OutsideForthelEnv
  NonTex -> tokenize TexDisabled

-- launch a parser in the IO monad
launchParser :: Parser st a -> State st -> IO (a, State st)
launchParser parser state =
  case runP parser state of
    Error err -> Message.errorParser (errorPos err) (show_bytes err)
    Ok [PR a st] -> return (a, st)
