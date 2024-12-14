-- |
-- Module      : SAD.Import.Reader
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Main text reading functions.


module SAD.Import.Reader (
  readProofText
) where

import Prelude hiding (read, readFile)
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
import SAD.Parser.FTL.Lexer qualified as FTL
import SAD.Parser.TEX.Lexer qualified as TEX
import SAD.Parser.FTL.Token qualified as FTL
import SAD.Parser.TEX.Token qualified as TEX
import SAD.Parser.Token (Token, noTokens)
import SAD.Core.Message qualified as Message

import Isabelle.File qualified as File
import Isabelle.Library (make_bytes, getenv, make_string)
import Isabelle.Position as Position
import Isabelle.Bytes (Bytes)

import Naproche.Program qualified as Program


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
          (newProofText, newState) <- parse pState
          go (newState:states) newProofText
      | otherwise = do
          let filePath = Text.unpack file
          text <- Text.pack <$>
            catch (if Text.null file then getContents else make_string <$> File.read filePath)
              (Message.errorParser (Position.file_only $ make_bytes file) . make_bytes . ioeGetErrorString)
          (newProofText, newState) <- readFile parserKind' filePath text pState
          -- state from before reading is still here
          reader pathToLibrary (file:doneFiles) (newState:pState:states) newProofText

    go (pState:states) [ProofTextInstr _ (GetArgument (Text pk) text)] = do
      (newProofText, newState) <- readText pk text pState
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
      (newProofText, newState) <- parse resetState
      go (newState:rest) newProofText

    go (state:_) [] = return ([], reports $ stUser state)

    go _ _ = error $ "SAD.Parser.Base.reader: Invalid arguments for function \"go\". " <>
      "If you see this message, please file an issue."

read :: ParserKind -> Position.T -> Bytes -> State FState -> IO ([ProofText], State FState)
read dialect pos bytes state = do
  tokens <- case dialect of
    Ftl -> FTL.lex pos bytes >>= FTL.tokenize
    Tex -> TEX.lex pos bytes >>= TEX.tokenize
  let newState = State {
        stUser = addInits dialect $ (stUser state) {tvrExpr = []},
        stInput = tokens,
        parserKind = dialect,
        lastPosition = Position.none
      }
  parse newState

-- | Read a text.
readText :: ParserKind -> Text -> State FState -> IO ([ProofText], State FState)
readText dialect text state =
  read dialect Position.start (make_bytes text) (state {parserKind = dialect})

-- | Read a file
readFile :: ParserKind -> FilePath -> Text -> State FState -> IO ([ProofText], State FState)
readFile dialect filePath text state =
  read dialect (Position.file $ make_bytes filePath) (make_bytes text) (state {parserKind = dialect})

-- | Parse (the tokens contained in) a state.
parse :: State FState -> IO ([ProofText], State FState)
parse state =
  let dialect = parserKind state
      parser = case dialect of
        Ftl -> forthelFtl
        Tex -> forthelTex
  in launchParser parser state

initState :: Program.Context -> [Token] -> State FState
initState context tokens = State (initFState context) tokens Ftl Position.none
