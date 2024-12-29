-- |
-- Module      : SAD.Import.Reader
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Main text reading functions.

module SAD.Import.Reader (
  readProofText
) where

import Control.Monad
import System.IO.Error
import System.FilePath
import Control.Exception

import SAD.Data.Text.Block
import SAD.Data.Instr
import SAD.ForTheL.Base
import SAD.ForTheL.Structure
import SAD.Parser.Base
import SAD.Parser.FTL.Lexer qualified as FTL
import SAD.Parser.TEX.Lexer qualified as TEX
import SAD.Parser.FTL.Token qualified as FTL
import SAD.Parser.TEX.Token qualified as TEX
import SAD.Parser.Token (Token, noTokens)
import SAD.Core.Message qualified as Message
import SAD.Helpers (failWithMessage)

import Isabelle.File qualified as File
import Isabelle.Library (make_bytes, getenv, make_string)
import Isabelle.Position as Position
import Isabelle.Bytes (Bytes)

import Naproche.Program qualified as Program


-- * Reader loop

-- | Parse one or more ForTheL texts
readProofText :: ParserKind -> [ProofText] -> IO [ProofText]
readProofText dialect text0 = do
  context <- Program.thread_context
  pathToLibrary <- getPathToLibrary
  (text, reports) <- reader dialect pathToLibrary [] [initState context noTokens] text0
  when (Program.is_pide context) $ Message.reports reports
  return text

reader :: ParserKind -> FilePath -> [FilePath] -> [State FState] -> [ProofText] -> IO ([ProofText], [Position.Report])
-- Take an archive path, a module path and a module name, turn it into an
-- absolute file path and continue the reader loop with a read instruction for
-- this file path.
reader dialect pathToLibrary doneFiles stateList [ProofTextInstr pos (GetModule archivePath modulePath moduleName)] =
  let relativeFilePath = archivePath </> "source" </> modulePath </> moduleName
      relativeFilePath' = case dialect of
        Ftl -> relativeFilePath
        Tex -> relativeFilePath <.> "tex"
      absoluteFilePath = pathToLibrary </> relativeFilePath'
      instr = GetAbsoluteFilePath absoluteFilePath
  in reader dialect pathToLibrary doneFiles stateList [ProofTextInstr pos instr]
-- Take a relative file path (i.e. relative to the library directory) and turn
-- it into an absolute path.
reader dialect pathToLibrary doneFiles stateList [ProofTextInstr pos (GetRelativeFilePath relativeFilePath)]
  -- Catch "." as directory name in file path:
  | "." `elem` splitDirectories relativeFilePath =
      Message.errorParser pos $
        "\".\" is not allowed as a directory name in a file path: " ++
        relativeFilePath
  -- Catch ".." as directory name in file path:
  | ".." `elem` splitDirectories relativeFilePath =
      Message.errorParser pos $
        "\"..\" is not allowed as a directory name in a file path: " ++
        relativeFilePath
  -- Catch invalid file name extension:
  | takeExtensions relativeFilePath `notElem` [".ftl", ".ftl.tex"] =
      Message.errorParser pos $
        "Invalid file name extension \"" ++ takeExtensions relativeFilePath ++
        "\": " ++ relativeFilePath
  -- Catch .ftl file read from within a text written in the TEX dialect:
  | takeExtensions relativeFilePath == ".ftl" && dialect == Tex =
      Message.errorParser pos $
        "Invalid read instruction for a \".ftl\" file in a \".ftl.tex\" text: "
        ++ relativeFilePath
  -- Catch .ftl.tex file read from within a text written in the FTL dialect:
  | takeExtensions relativeFilePath == ".ftl.tex" && dialect == Ftl =
      Message.errorParser pos $
        "Invalid read instruction for a \".ftl.tex\" file in a \".ftl\" text: "
        ++ relativeFilePath
  | otherwise =
      let absoluteFilePath = pathToLibrary </> relativeFilePath
          instr = GetAbsoluteFilePath absoluteFilePath
      in reader dialect pathToLibrary doneFiles stateList [ProofTextInstr pos instr]

reader dialect pathToLibrary doneFiles (pState : states) [ProofTextInstr pos (GetAbsoluteFilePath absoluteFilePath)]
  | absoluteFilePath `elem` doneFiles = do
      Message.outputMain Message.WARNING pos
        (make_bytes ("Skipping already read file: " ++ absoluteFilePath))
      (newProofText, newState) <- parseState pState
      reader dialect pathToLibrary doneFiles (newState:states) newProofText
  | otherwise = do
      (newProofText, newState) <- parseFile dialect absoluteFilePath pState
      -- state from before reading is still here
      reader dialect pathToLibrary (absoluteFilePath : doneFiles) (newState:pState:states) newProofText

reader dialect pathToLibrary doneFiles (pState : states) [ProofTextInstr pos (GetText text)] = do
    (newProofText, newState) <- parseBytes dialect text pState
    reader dialect pathToLibrary doneFiles (newState : pState : states) newProofText -- state from before reading is still here

-- This says that we are only really processing the last instruction in a [ProofText].
reader dialect pathToLibrary doneFiles stateList (t : restProofText) = do
  (ts, ls) <- reader dialect pathToLibrary doneFiles stateList restProofText
  return (t : ts, ls)

reader dialect pathToLibrary doneFiles (pState : oldState : rest) [] = do
  Message.outputParser Message.TRACING
    (if null doneFiles then Position.none else Position.file_only $ make_bytes $ head doneFiles) "parsing successful"
  let resetState = oldState {
        stUser = (stUser pState) {tvrExpr = tvrExpr $ stUser oldState}}
  -- Continue running a parser after eg. a read instruction was evaluated.
  (newProofText, newState) <- parseState resetState
  reader dialect pathToLibrary doneFiles (newState : rest) newProofText

reader _ _ _ (state : _) [] = return ([], reports $ stUser state)

reader _ _ _ _ _ = failWithMessage "SAD.Parser.Base.reader" "Invalid arguments."

-- | Consequtively lex, tokenize and parse a byte string.
parse :: ParserKind -> Position.T -> Bytes -> State FState -> IO ([ProofText], State FState)
parse dialect pos bytes state = do
  tokens <- case dialect of
    Ftl -> FTL.lex pos bytes >>= FTL.tokenize
    Tex -> TEX.lex pos bytes >>= TEX.tokenize
  let newState = State {
        stUser = addInits dialect $ (stUser state) {tvrExpr = []},
        stInput = tokens,
        parserKind = dialect,
        lastPosition = Position.none
      }
  parseState newState

-- | Parse a byte string.
parseBytes :: ParserKind -> Bytes -> State FState -> IO ([ProofText], State FState)
parseBytes dialect bytes state =
  let pos = Position.start
  in parse dialect pos bytes state{parserKind = dialect}

-- | Parse a file (or the content of stdin if an empty file path is given).
parseFile :: ParserKind -> FilePath -> State FState -> IO ([ProofText], State FState)
parseFile dialect filePath state = do
  bytes <- catch
    (if null filePath then make_bytes <$> getContents else File.read filePath)
    (Message.errorParser (Position.file_only $ make_bytes filePath) . make_bytes . ioeGetErrorString)
  let pos = Position.file $ make_bytes filePath
  parse dialect pos bytes state{parserKind = dialect}

-- | Parse (the tokens contained in) a state.
parseState :: State FState -> IO ([ProofText], State FState)
parseState state =
  let dialect = parserKind state
      parser = case dialect of
        Ftl -> forthelFtl
        Tex -> forthelTex
  in launchParser parser state

initState :: Program.Context -> [Token] -> State FState
initState context tokens = State (initFState context) tokens Ftl Position.none

-- | Get the path to the formalizations library.
getPathToLibrary :: IO FilePath
getPathToLibrary = make_string <$> getenv libraryEnvVar

-- | The name of the environment variable that contains the path to the
-- formalizations library.
-- **NOTE:** This name must coincide with the one given in @etc/settings@!
libraryEnvVar :: Bytes
libraryEnvVar = make_bytes "NAPROCHE_FORMALIZATIONS"
