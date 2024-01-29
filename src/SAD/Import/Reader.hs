-- |
-- Authors: Andrei Paskevich (2001 - 2008),
--          Steffen Frerix (2017 - 2018)
--
-- Main text reading functions.


{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module SAD.Import.Reader (
  readInit,
  readProofText
) where

import Control.Monad
import System.IO.Error
import Control.Exception
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.Data.Text.Block
import SAD.Data.Instr as Instr
    ( Argument(Text, File, Read),
      ParserKind(..),
      Instr(GetArgument))
import SAD.ForTheL.Base
import SAD.ForTheL.Structure
import SAD.Parser.Base
import SAD.ForTheL.Instruction
import SAD.Parser.Token
import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.Parser.Error
import SAD.Lexer.FTL qualified as FTL
import SAD.Lexer.TEX qualified as TEX
import SAD.Core.Message qualified as Message

import Isabelle.File qualified as File
import Isabelle.Library (make_bytes, make_string, make_text, show_bytes)
import Isabelle.Position as Position
import Isabelle.Bytes (Bytes)
import Isabelle.Bytes qualified as Bytes

import Naproche.Program qualified as Program


-- * Init file parsing

-- | Parse initial instructions (e.g. @$NAPROCHE_HOME/init.opt@)
readInit :: Bytes -> IO [(Position.T, Instr)]
readInit file | Bytes.null file = return []
readInit file = do
  input <- catch (File.read (make_string file)) $ Message.errorParser (Position.file_only $ make_bytes file) . make_bytes . ioeGetErrorString
  tokens <- FTL.tokenize (Position.file $ make_bytes file) $ Text.fromStrict $ make_text input
  fst <$> launchParser instructionFile (initState Program.console tokens)

instructionFile :: FTL [(Position.T, Instr)]
instructionFile = after (optLL1 [] $ chainLL1 instr) eof

initState :: Program.Context -> [Token] -> State FState
initState context tokens = State (initFState context) tokens Ftl Position.none


-- * Reader loop

-- | Parse one or more ForTheL texts
readProofText :: Bytes          -- ^ path to library from where other ForTheL
                                -- texts can be imported via @read(tex)@
                                -- instructions (e.g. @$NAPROCHE_HOME/examples)
              -> [ProofText]    -- ^ ForTheL texts to be parsed
              -> IO [ProofText]
readProofText pathToLibrary text0 = do
  context <- Program.thread_context
  (text, reports) <- reader pathToLibrary [] [initState context noTokens] text0
  when (Program.is_pide context) $ Message.reports reports
  return text

reader :: Bytes -> [Text] -> [State FState] -> [ProofText] -> IO ([ProofText], [Position.Report])
reader pathToLibrary doneFiles = go
  where
    go stateList [ProofTextInstr pos (GetArgument (Read pk) file)] = if Text.pack ".." `Text.isInfixOf` file
      then Message.errorParser pos ("Illegal \"..\" in file name: " ++ show file)
      else go stateList [ProofTextInstr pos $ GetArgument (File pk) $
            Text.pack (make_string pathToLibrary) <> Text.pack "/" <> file]

    go (pState:states) [ProofTextInstr pos (GetArgument (File parserKind') file)]
      | file `elem` doneFiles = do
          -- The parserKind of the state of the parser indicates whether the file was originally read with the .tex
          -- or the .ftl parser. Now if, for example, we originally read the file with the .ftl format and now we
          -- are reading the file again with the .tex format(by eg using '[readtex myfile.ftl]'), we want to throw an error.
          when (parserKind pState /= parserKind')
            (Message.errorParser pos "Trying to read the same file once in TEX format and once in FTL format.")
          Message.outputMain Message.WARNING pos
            (make_bytes ("Skipping already read file: " ++ show file))
          (newProofText, newState) <- chooseParser pState
          go (newState:states) newProofText
      | otherwise = do
          text <-
            catch (if Text.null file then getContents else make_string <$> File.read (Text.unpack file))
              (Message.errorParser (Position.file_only $ make_bytes file) . make_bytes . ioeGetErrorString)
          (newProofText, newState) <- parse (Position.file $ make_bytes file) (Text.pack text) (pState {parserKind = parserKind'})
          -- state from before reading is still here
          reader pathToLibrary (file:doneFiles) (newState:pState:states) newProofText

    go (pState:states) [ProofTextInstr _ (GetArgument (Text pk) text)] = do
      (newProofText, newState) <- parse Position.start text (pState {parserKind = pk})
      go (newState:pState:states) newProofText -- state from before reading is still here

    -- This says that we are only really processing the last instruction in a [ProofText].
    go stateList (t:restProofText) = do
      (ts, ls) <- go stateList restProofText
      return (t:ts, ls)

    go (pState:oldState:rest) [] = do
      Message.outputParser Message.TRACING
        (if null doneFiles then Position.none else Position.file_only $ make_bytes $ head doneFiles) "parsing successful"
      let resetState = oldState {
            stUser = (stUser pState) {tvrExpr = tvrExpr $ stUser oldState}}
      -- Continue running a parser after eg. a read instruction was evaluated.
      (newProofText, newState) <- chooseParser resetState
      go (newState:rest) newProofText

    go (state:_) [] = return ([], reports $ stUser state)


-- * Parsing

-- | Parse a ForTheL Text with a given starting position and a parser state.
parse :: Position.T -> Text -> State FState -> IO ([ProofText], State FState)
parse startPos text parserState = do
  let dialect = parserKind parserState
  tokens <- case dialect of
    Ftl -> FTL.tokenize startPos text
    Tex -> TEX.tokenize startPos text
  let initParserState = State {
    stUser  = addInits dialect ((stUser parserState) {tvrExpr = []}),
    stInput = tokens,
    parserKind = dialect,
    lastPosition = Position.none
  }
  chooseParser initParserState

-- | Lauch the ForTheL parser wrt. the dialect given by in the current parser
-- state.
chooseParser :: State FState -> IO ([ProofText], State FState)
chooseParser st = let dialect = parserKind st in
  launchParser (forthel dialect) st

-- Launch a parser in the IO monad.
launchParser :: Parser st a -> State st -> IO (a, State st)
launchParser parser state =
  case runP parser state of
    Error err -> Message.errorParser (errorPos err) (show_bytes err)
    Ok [PR a st] -> return (a, st)
