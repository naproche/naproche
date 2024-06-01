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
      ParserKind(Ftl,Tex),
      Instr(GetArgument))
import SAD.ForTheL.Base
import SAD.ForTheL.Structure
import SAD.Parser.Base
import SAD.ForTheL.Instruction
import SAD.Parser.Lexer
import SAD.Parser.Token (Token, ftlLexemesToTokens, texLexemesToTokens, noTokens)
import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.Parser.Error
import SAD.Core.Message qualified as Message

import Isabelle.File qualified as File
import Isabelle.Library (make_bytes, getenv, make_string, make_text, show_bytes)
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
  let pos = Position.file $ make_bytes file
      text = Text.fromStrict $ make_text input
  lexemes <- lexFtl (PIDE_Pos pos) text
  tokens <- ftlLexemesToTokens lexemes
  fst <$> launchParser instructionFile (initState Program.console tokens)

instructionFile :: FTL [(Position.T, Instr)]
instructionFile = after (optLL1 [] $ chainLL1 instr) eof

initState :: Program.Context -> [Token] -> State FState
initState context tokens = State (initFState context) tokens Ftl Position.none


-- * Reader loop

-- | Parse one or more ForTheL texts
readProofText :: Bytes          -- ^ name of enviroment variable containing
                                -- path to formalizations directory
                                -- texts can be imported via @read(tex)@
                                -- instructions (e.g. @$NAPROCHE_HOME/examples)
              -> [ProofText]    -- ^ ForTheL texts to be parsed
              -> IO [ProofText]
readProofText variable text0 = do
  context <- Program.thread_context
  path <- getenv variable
  (text, reports) <- reader path [] [initState context noTokens] text0
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
          (newProofText, newState) <- reader0 (Position.file $ make_bytes file) (Text.pack text) (pState {parserKind = parserKind'})
          -- state from before reading is still here
          reader pathToLibrary (file:doneFiles) (newState:pState:states) newProofText

    go (pState:states) [ProofTextInstr _ (GetArgument (Text pk) text)] = do
      (newProofText, newState) <- reader0 Position.start text (pState {parserKind = pk})
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

reader0 :: Position.T -> Text -> State FState -> IO ([ProofText], State FState)
reader0 pos text pState = do
  let dialect = parserKind pState
  tokens <- case dialect of
    Ftl -> lexFtl (PIDE_Pos pos) text >>= ftlLexemesToTokens
    Tex -> lexTex (PIDE_Pos pos) text >>= texLexemesToTokens
  let st = State
        (addInits dialect ((stUser pState) {tvrExpr = []}))
        tokens
        dialect
        Position.none
  chooseParser st


chooseParser :: State FState -> IO ([ProofText], State FState)
chooseParser st = let dialect = parserKind st in
  launchParser (forthel dialect) st

-- Launch a parser in the IO monad.
launchParser :: Parser st a -> State st -> IO (a, State st)
launchParser parser state =
  case runP parser state of
    Error err -> Message.errorParser (errorPos err) (show_bytes err)
    Ok [PR a st] -> return (a, st)
