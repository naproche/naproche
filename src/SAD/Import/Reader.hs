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
import System.FilePath.Posix
import Control.Exception

import SAD.Data.Text.Block
import SAD.Data.Instr
import SAD.ForTheL.Base
import SAD.ForTheL.FTL.Base qualified as FTL
import SAD.ForTheL.FTL.Structure qualified as FTL
import SAD.ForTheL.TEX.Base qualified as TEX
import SAD.ForTheL.TEX.Structure qualified as TEX
import SAD.ForTheL.STEX.Base qualified as STEX
import SAD.ForTheL.STEX.Structure qualified as STEX
import SAD.Parser.Base
import SAD.Parser.FTL.Lexer qualified as FTL
import SAD.Parser.TEX.Lexer qualified as TEX
import SAD.Parser.STEX.Lexer qualified as STEX
import SAD.Parser.FTL.Token qualified as FTL
import SAD.Parser.TEX.Token qualified as TEX
import SAD.Parser.STEX.Token qualified as STEX
import SAD.Parser.Token (Token, noTokens)
import SAD.Core.Message qualified as Message
import SAD.Helpers (failWithMessage, getNaprocheFormalizations)

import Isabelle.File qualified as File
import Isabelle.Library (make_bytes)
import Isabelle.Position as Position
import Isabelle.Bytes (Bytes)

import Naproche.Program qualified as Program


-- * Reader loop

-- | Parse one or more ForTheL texts
readProofText :: ParserKind -> [ProofText] -> IO [ProofText]
readProofText dialect text0 = do
  context <- Program.thread_context
  naprocheFormalizationsPath <- getNaprocheFormalizations
  (text, reports) <- reader 0 dialect naprocheFormalizationsPath [] [initState context noTokens] text0
  when (Program.is_pide context) $ Message.reports reports
  return text

reader :: Int -> ParserKind -> FilePath -> [FilePath] -> [State FState] -> [ProofText] -> IO ([ProofText], [Position.Report])
-- Take an archive path, a module path and a module name, turn it into an
-- absolute file path and continue the reader loop with a read instruction for
-- this file path.
-- Moreover, we track the depth of the imported modules (where depth 0 means
-- that we are currently not in an imported module), where we disable the
-- logical and ontological checking at depth > 0.
reader depth dialect naprocheFormalizationsPath doneFiles stateList [ProofTextInstr pos (GetModule archivePath modulePath moduleName)] =
  let relativeFilePath = archivePath </> "source" </> modulePath </> moduleName
      relativeFilePath' = relativeFilePath <.> "en" <.> "tex"
      absoluteFilePath = naprocheFormalizationsPath </> "archive" </> relativeFilePath'
      instr = GetAbsoluteFilePath absoluteFilePath
  in do
    (proofTexts, reports) <- reader (depth + 1) dialect naprocheFormalizationsPath doneFiles stateList [ProofTextInstr pos instr]
    let proofTexts' = if depth == 0
          then [
              ProofTextInstr Position.none (SetBool proveParam False),
              ProofTextInstr Position.none (SetBool checkParam False)
            ] ++ proofTexts ++ [
              ProofTextInstr Position.none (SetBool proveParam True),
              ProofTextInstr Position.none (SetBool checkParam True)
            ]
          else proofTexts
    return (proofTexts', reports)
-- Take a relative file path (i.e. relative to the library directory) and turn
-- it into an absolute path.
reader depth dialect naprocheFormalizationsPath doneFiles stateList [ProofTextInstr pos (GetRelativeFilePath relativeFilePath)]
  -- Catch "." as directory name in file path:
  | "." `elem` splitDirectories relativeFilePath =
      Message.errorReader pos $
        "\".\" is not allowed as a directory name in a file path: " ++
        relativeFilePath
  -- Catch ".." as directory name in file path:
  | ".." `elem` splitDirectories relativeFilePath =
      Message.errorReader pos $
        "\"..\" is not allowed as a directory name in a file path: " ++
        relativeFilePath
  -- Catch invalid file name extension:
  | (takeExtensions relativeFilePath `notElem` [".ftl", ".ftl.tex", ".ftl.en.tex"])
      || (takeExtensions relativeFilePath == ".ftl" && dialect /= Ftl)
      || (takeExtensions relativeFilePath == ".ftl.tex" && dialect /= Tex)
      || (takeExtensions relativeFilePath == ".ftl.en.tex" && dialect /= Stex)
     = Message.errorReader pos $
        "Invalid file name extension \"" ++ takeExtensions relativeFilePath ++
        "\": " ++ relativeFilePath
  | otherwise =
      let absoluteFilePath = naprocheFormalizationsPath </> relativeFilePath
          instr = GetAbsoluteFilePath absoluteFilePath
      in do
        (proofTexts, reports) <- reader (depth + 1) dialect naprocheFormalizationsPath doneFiles stateList [ProofTextInstr pos instr]
        let proofTexts' = if depth == 0
            then [
                ProofTextInstr Position.none (SetBool proveParam False),
                ProofTextInstr Position.none (SetBool checkParam False)
              ] ++ proofTexts ++ [
                ProofTextInstr Position.none (SetBool proveParam True),
                ProofTextInstr Position.none (SetBool checkParam True)
              ]
            else proofTexts
        return (proofTexts', reports)

reader depth dialect naprocheFormalizationsPath doneFiles (pState : states) [ProofTextInstr pos (GetAbsoluteFilePath absoluteFilePath)]
  | absoluteFilePath `elem` doneFiles = do
      (newProofText, newState) <- parseState pState
      reader (depth - 1) dialect naprocheFormalizationsPath doneFiles (newState:states) newProofText
  | otherwise = do
      (newProofText, newState) <- parseFile dialect absoluteFilePath pState
      let newProofText' = if depth > 0
          then [
              ProofTextInstr Position.none (SetBool proveParam False),
              ProofTextInstr Position.none (SetBool checkParam False)
            ] ++ newProofText
          else newProofText
      -- state from before reading is still here
      reader depth dialect naprocheFormalizationsPath (absoluteFilePath : doneFiles) (newState:pState:states) newProofText'

reader depth dialect naprocheFormalizationsPath doneFiles (pState : states) [ProofTextInstr pos (GetText text)] = do
    (newProofText, newState) <- parseBytes dialect text pState
    reader depth dialect naprocheFormalizationsPath doneFiles (newState : pState : states) newProofText -- state from before reading is still here

-- This says that we are only really processing the last instruction in a [ProofText].
reader depth dialect naprocheFormalizationsPath doneFiles stateList (t : restProofText) = do
  (ts, ls) <- reader depth dialect naprocheFormalizationsPath doneFiles stateList restProofText
  return (t : ts, ls)

reader depth dialect naprocheFormalizationsPath doneFiles (pState : oldState : rest) [] = do
  Message.outputParser Message.TRACING
    (if null doneFiles then Position.none else Position.file_only $ make_bytes $ head doneFiles) "parsing successful"
  let resetState = oldState {
        stUser = (stUser pState) {tvrExpr = tvrExpr $ stUser oldState}}
  -- Continue running a parser after eg. a read instruction was evaluated.
  (newProofText, newState) <- parseState resetState
  (newProofText', reports) <- reader (if depth == 0 then 0 else depth - 1) dialect naprocheFormalizationsPath doneFiles (newState : rest) newProofText
  let newProofText'' = if depth == 1
        then [
            ProofTextInstr Position.none (SetBool proveParam True),
            ProofTextInstr Position.none (SetBool checkParam True)
          ] ++ newProofText'
        else newProofText'
  return (newProofText'', reports)


reader _ _ _ _ (state : _) [] = return ([], reports $ stUser state)

reader _ _ _ _ _ _ = failWithMessage "SAD.Parser.Base.reader" "Invalid arguments."

-- | Consequtively lex, tokenize and parse a byte string.
parse :: ParserKind -> Position.T -> Bytes -> State FState -> IO ([ProofText], State FState)
parse dialect pos bytes state = do
  tokens <- case dialect of
    Ftl -> FTL.lex pos bytes >>= FTL.tokenize
    Tex -> TEX.lex pos bytes >>= TEX.tokenize
    Stex -> STEX.lex pos bytes >>= STEX.tokenize
  let 
      addInits = case dialect of
        Ftl -> FTL.addInits
        Tex -> TEX.addInits
        Stex -> STEX.addInits
      newState = State {
        stUser = addInits $ (stUser state) {tvrExpr = []},
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
    (Message.errorReader (Position.file_only $ make_bytes filePath) . make_bytes . ioeGetErrorString)
  let pos = Position.file $ make_bytes filePath
  parse dialect pos bytes state{parserKind = dialect}

-- | Parse (the tokens contained in) a state.
parseState :: State FState -> IO ([ProofText], State FState)
parseState state =
  let dialect = parserKind state
      parser = case dialect of
        Ftl -> FTL.forthelText
        Tex -> TEX.forthelText
        Stex -> STEX.forthelText
  in launchParser parser state

initState :: Program.Context -> [Token] -> State FState
initState context tokens = State (initFState context) tokens Ftl Position.none


