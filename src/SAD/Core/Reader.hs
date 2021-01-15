{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Main text reading functions.
-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.Reader (HasLibrary(..), withLibrary, parseInit, readProofText) where

import Data.Maybe
import Control.Monad
import System.IO.Error
import Control.Exception
import Data.Text (Text)
import qualified Data.Text as Text
import Control.Monad.Reader
import Control.Monad.State (StateT)

import SAD.Data.Text.Block
import SAD.Data.Instr as Instr
    ( Argument(Text, File, Read),
      ParserKind(Tex, NonTex),
      Instr(GetArgument),
      Pos,
      position )
import SAD.ForTheL.Base
import SAD.ForTheL.Structure (forthel, texForthel)
import SAD.Parser.Base
import SAD.ForTheL.Instruction
import SAD.Core.SourcePos
import SAD.Parser.Token
import SAD.Parser.Combinators (after, optLL1, chainLL1)
import SAD.Parser.Primitives
import SAD.Parser.Error
import qualified SAD.Core.Message as Message
import qualified Isabelle.File as File
import System.FilePath
import System.Directory
import SAD.Core.Prove (RunProver)
import SAD.Core.Cache (CacheStorage)

class Monad m => HasLibrary m where
  -- | Read a file in the library
  readLibrary :: FilePath -> m Text

newtype WithLibrary a = WithLibrary { fromWithLibrary :: ReaderT FilePath IO a }
  deriving (Functor, Applicative, Monad, MonadReader FilePath, MonadIO, Message.Comm, RunProver, CacheStorage)

instance HasLibrary m => HasLibrary (StateT s m) where
  readLibrary = lift . readLibrary

instance HasLibrary WithLibrary where
  readLibrary f = do
    ex_f <- liftIO $ doesFileExist f
    library <- ask
    let file = if ex_f then f else library </> f
    liftIO $ fmap Text.pack $ catch (if null file then getContents else File.read file)
      (Message.errorParser (fileOnlyPos file) . ioeGetErrorString)

withLibrary :: FilePath -> WithLibrary a -> IO a
withLibrary f = flip runReaderT f . fromWithLibrary

-- | Parse the content of an "init.opt" file
parseInit :: Message.Comm m => FilePath -> Text -> m [(Pos, Instr)]
parseInit file input = do
  let tokens = filter isProperToken $ tokenize TexDisabled (filePos file) input
      initialParserState = State (initFS Nothing) tokens NonTex noSourcePos
  fst <$> launchParser instructionFile initialParserState

instructionFile :: FTL [(Pos, Instr)]
instructionFile = after (optLL1 [] $ chainLL1 instr) eof


-- Reader loop

-- | @readProofText startWithTex pathToLibrary text0@ takes:
-- @startWithTex@, a boolean indicating whether to execute the next file instruction using the tex parser,
-- @pathToLibrary@, a path to where the read instruction should look for files and
-- @text0@, containing some configuration.
readProofText :: (Message.Comm m, HasLibrary m) => [ProofText] -> m [ProofText]
readProofText text0 = do
  pide <- Message.pideContext
  (text, reports) <- readFtlFile [] [State (initFS pide) noTokens NonTex noSourcePos] text0
  when (isJust pide) $ Message.reports reports
  return text

readFtlFile :: (HasLibrary m, Message.Comm m) => [FilePath] -> [State FState] -> [ProofText] -> m ([ProofText], [Message.Report])
readFtlFile doneFiles = go
  where
    go stateList [ProofTextInstr pos (GetArgument (Read pk) file)] = if ".." `Text.isInfixOf` file
      then Message.errorParser (Instr.position pos) ("Illegal \"..\" in file name: " ++ show file)
      else go stateList [ProofTextInstr pos $ GetArgument (File pk) $ file]

    go (pState:states) [ProofTextInstr pos (GetArgument (File parserKind') file)]
      | (Text.unpack file) `elem` doneFiles = do
          -- The parserKind of the state of the parser indicates whether the file was originally read with the .tex
          -- or the .ftl parser. Now if, for example, we originally read the file with the .ftl format and now we
          -- are reading the file again with the .tex format(by eg using '[readtex myfile.ftl]'), we want to throw an error.
          when (parserKind pState /= parserKind')
            (Message.errorParser (Instr.position pos) "Trying to read the same file once in Tex format and once in NonTex format.")
          Message.outputMain Message.WARNING (Instr.position pos)
            ("Skipping already read file: " ++ show file)
          (newProofText, newState) <- chooseParser pState
          go (newState:states) newProofText
      | otherwise = do
          let file' = Text.unpack file
          text <- readLibrary file'
          (newProofText, newState) <- readFtlFile0 (filePos file') text (pState {parserKind = parserKind'})
          -- state from before reading is still here
          readFtlFile (file':doneFiles) (newState:pState:states) newProofText

    go (pState:states) [ProofTextInstr _ (GetArgument (Text pk) text)] = do
      (newProofText, newState) <- readFtlFile0 startPos text (pState {parserKind = pk})
      go (newState:pState:states) newProofText -- state from before reading is still here

    -- This says that we are only really processing the last instruction in a [ProofText].
    go stateList (t:restProofText) = do
      (ts, ls) <- go stateList restProofText
      return (t:ts, ls)

    go (pState:oldState:rest) [] = do
      Message.outputParser Message.TRACING
        (if null doneFiles then noSourcePos else fileOnlyPos $ head doneFiles) "parsing successful"
      let resetState = oldState {
            stUser = (stUser pState) {tvrExpr = tvrExpr $ stUser oldState}}
      -- Continue running a parser after eg. a read instruction was evaluated.
      (newProofText, newState) <- chooseParser resetState
      go (newState:rest) newProofText

    go (state:_) [] = return ([], reports $ stUser state)

readFtlFile0 :: Message.Comm m => SourcePos -> Text -> State FState -> m ([ProofText], State FState)
readFtlFile0 pos text pState = do
  let tokens0 = chooseTokenizer pState pos text
  Message.reports $ mapMaybe reportComments tokens0
  let tokens = filter isProperToken tokens0
      st = State ((stUser pState) { tvrExpr = [] }) tokens (parserKind pState) noSourcePos
  chooseParser st


chooseParser :: Message.Comm m => State FState -> m ([ProofText], State FState)
chooseParser st = case parserKind st of
  Tex -> launchParser texForthel st
  NonTex -> launchParser forthel st

chooseTokenizer :: State FState -> SourcePos -> Text -> [Token]
chooseTokenizer st = case parserKind st of
  Tex -> tokenize OutsideForthelEnv
  NonTex -> tokenize TexDisabled

launchParser :: Message.Comm m => Parser st a -> State st -> m (a, State st)
launchParser parser state =
  case runP parser state of
    Error err -> Message.errorParser (errorPos err) (show err)
    Ok [PR a st] -> return (a, st)
