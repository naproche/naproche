{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)
  Adrian Marti (2021), Anton Lorenzen (2020 - 2021)

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
import Data.Map (Map)
import qualified Data.Map as Map

import SAD.Data.Text.Block
import SAD.Data.Instr as Instr
    ( Argument(Text, Read),
      ParserKind(Tex, NonTex),
      Instr(GetArgument),
      Pos, position )
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
  -- | Read a relative filepath in the current paths
  -- and return its content and the matched filepath.
  readLibrary :: FilePath -> m (FilePath, Text)

newtype WithLibrary a = WithLibrary { fromWithLibrary :: ReaderT FilePath IO a }
  deriving (Functor, Applicative, Monad, MonadReader FilePath, MonadIO, Message.Comm, RunProver, CacheStorage)

instance HasLibrary m => HasLibrary (StateT s m) where
  readLibrary = lift . readLibrary

instance HasLibrary WithLibrary where
  readLibrary f
    --- This an be used for protection against attacks:
    --- | ".." `isInfixOf` f = 
    ---   Message.errorParser (fileOnlyPos f) ("Illegal \"..\" in file name: " ++ show f)
    | otherwise = do
      library <- ask
      ex_f <- liftIO $ doesFileExist f
      ex_lf <- liftIO $ doesFileExist $ library </> f
      file <- case (ex_f, ex_lf) of
        (True, _) -> pure f
        (_, True) -> pure $ library </> f
        _ -> Message.errorParser (fileOnlyPos f) $ "File not found! Neither " ++ f ++ " nor " ++ (library </> f)
          ++ " is a valid file path!"
      content <- liftIO $ fmap Text.pack $ catch (if null file then getContents else File.read file)
        (Message.errorParser (fileOnlyPos file) . ioeGetErrorString)
      pure (file, content)

withLibrary :: FilePath -> WithLibrary a -> IO a
withLibrary f = flip runReaderT f . fromWithLibrary

-- | Parse the content of an "init.opt" file
parseInit :: Message.Comm m => FilePath -> Text -> m [(Pos, Instr)]
parseInit file input = do
  let tokens = filter isProperToken $ tokenize TexDisabled (filePos file) input
      initialParserState = State (initFS Nothing) tokens NonTex noSourcePos
      instructionFile = after (optLL1 [] $ chainLL1 instr) eof
  fst <$> launchParser instructionFile initialParserState

-- | Get the final read instruction from a sequence of proof texts.
getReadInstr :: [ProofText] -> (Maybe (ParserKind, Pos, Either FilePath Text), [ProofText])
getReadInstr ps =
  let (l, ls) = splitLast ps
      l' = case l of
        [ProofTextInstr pos (GetArgument (Read pk) file)] -> Just (pk, pos, Left $ Text.unpack file)
        [ProofTextInstr pos (GetArgument (Text pk) txt)] -> Just (pk, pos, Right txt)
        _ -> Nothing
  in (l', if isNothing l' then ps else ls)
  where
    splitLast [] = ([], [])
    splitLast [x] = ([x], [])
    splitLast (x:xs) = (x:) <$> splitLast xs

-- | Resolve the last instruction if it is a Read or Text instruction.
readProofText :: (Message.Comm m, HasLibrary m) => [ProofText] -> m [ProofText]
readProofText text0 = do
  let (mReadInstr, rest) = getReadInstr text0
  case mReadInstr of
    Nothing -> pure $ rest
    Just (pk, pos, eft) -> do
      pide <- Message.pideContext
      (_, (text, reports)) <- readFtlFile pide pk mempty pos eft
      when (isJust pide) $ Message.reports reports
      pure $ rest ++ text

-- | Resolve a single Read or Text instruction.
readFtlFile :: (HasLibrary m, Message.Comm m) => Maybe Message.PIDE -> ParserKind 
  -> Map FilePath (State FState, ([ProofText], [Message.Report])) 
  -> Pos -> Either FilePath Text -> m (State FState, ([ProofText], [Message.Report]))
readFtlFile pide pk doneFiles pos = \case
  (Left file) -> case Map.lookup file doneFiles of
    Just (state', res) -> do
        -- If, for example, we originally read the file with the .ftl format and now we
        -- are reading the file again with the .tex format(by eg using '[readtex myfile.ftl]'), we want to throw an error.
      when (parserKind state' /= pk)
        (Message.errorParser (Instr.position pos) "Trying to read the same file once in Tex format and once in NonTex format.")
      pure (state', ([], []))
    Nothing -> do
      (file', text) <- readLibrary file
      (newProofText, newState) <- beginParsing (filePos file') text initState 
      res <- cont doneFiles newState (filePos file') newProofText
      Message.outputParser Message.TRACING (fileOnlyPos file') "parsing successful"
      pure res
  (Right text) -> do
    (newProofText, newState) <- beginParsing startPos text initState 
    cont doneFiles newState startPos newProofText
  where
    initState = (State (initFS pide) noTokens pk noSourcePos)
    cont doneFiles state pos newProofText = do
      let (mRead, rest) = getReadInstr newProofText
      case mRead of
        Nothing -> pure $ (state, (rest, reports $ stUser state))
        Just (pk', pos', eft') -> do
          sub@(st, (ps, rs)) <- readFtlFile pide pk' doneFiles pos' eft'
          let doneFiles' = case eft' of
                  Left f -> Map.insert f sub doneFiles
                  _ -> doneFiles
          let state' = state { stUser = stUser st `appendTo` stUser state }
          (newProofText', newState) <- continueParsing state'
          (st', (ps', rs')) <- cont doneFiles' newState pos newProofText'
          pure $ (st', (rest ++ ps ++ ps', reports (stUser state) ++ rs ++ rs'))

-- | Given an fstate and a source position for tokenizing, parse the given text
-- until (including) the first read instruction or the end of the file.
beginParsing :: Message.Comm m => SourcePos -> Text -> State FState -> m ([ProofText], State FState)
beginParsing pos text pState = do
  let tokens0 = case parserKind pState of
          Tex -> tokenize OutsideForthelEnv pos text
          NonTex -> tokenize TexDisabled pos text
  Message.reports $ mapMaybe reportComments tokens0
  let tokens = filter isProperToken tokens0
      st = State ((stUser pState) { tvrExpr = [] }) tokens (parserKind pState) pos
  continueParsing st

-- | Continue parsing after the parsing was suspended by a read instruction.
continueParsing :: Message.Comm m => State FState -> m ([ProofText], State FState)
continueParsing st = case parserKind st of
  Tex -> launchParser texForthel st
  NonTex -> launchParser forthel st

-- | Run a given parser
launchParser :: Message.Comm m => Parser st a -> State st -> m (a, State st)
launchParser parser state =
  case runP parser state of
    Error err -> Message.errorParser (errorPos err) (show err)
    Ok [PR a st] -> return (a, st)