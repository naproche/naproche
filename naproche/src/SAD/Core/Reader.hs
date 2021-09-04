{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)
  Adrian Marti (2021), Anton Lorenzen (2020 - 2021)

Main text reading functions.
-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.Reader (HasLibrary(..), readProofText) where

import Data.Maybe
import Control.Monad
import Data.Text (Text)
import qualified Data.Text as Text
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
import SAD.Data.SourcePos
import SAD.Parser.Token
import SAD.Parser.Error
import SAD.Data.Message (Comm, PIDE, Report, pideContext, errorParser, outputParser, Kind(..), reportMeta)

class Monad m => HasLibrary m where
  -- | Read a relative filepath in the current paths
  -- and return its content and the matched filepath.
  readLibrary :: FilePath -> m (FilePath, Text)

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
-- TODO: Keep this in file batches so that unnamed lemmata can be removed
-- in imported files.
readProofText :: (Comm m, HasLibrary m) => [ProofText] -> m [ProofText]
readProofText text0 = do
  let (mReadInstr, rest) = getReadInstr text0
  case mReadInstr of
    Nothing -> pure $ rest
    Just (pk, pos, eft) -> do
      pide <- pideContext
      (_, (text, rs)) <- readFtlFile pide pk mempty pos eft
      when (isJust pide) $ reportMeta rs
      pure $ rest ++ text

-- | Resolve a single Read or Text instruction.
readFtlFile :: (HasLibrary m, Comm m) => Maybe PIDE -> ParserKind 
  -> Map FilePath (State FState, ([ProofText], [Report])) 
  -> Pos -> Either FilePath Text -> m (State FState, ([ProofText], [Report]))
readFtlFile pide pk doneFiles pos = \case
  (Left file) -> case Map.lookup file doneFiles of
    Just (state', _) -> do
        -- If, for example, we originally read the file with the .ftl format and now we
        -- are reading the file again with the .tex format(by eg using '[readtex myfile.ftl]'), we want to throw an error.
      when (parserKind state' /= pk)
        (errorParser (Instr.position pos) "Trying to read the same file once in Tex format and once in NonTex format.")
      pure (state', ([], []))
    Nothing -> do
      (file', text) <- readLibrary file
      (newProofText, newState) <- beginParsing (filePos file') text initState 
      res <- cont doneFiles newState (filePos file') newProofText
      outputParser TRACING (fileOnlyPos file') "parsing done"
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
beginParsing :: Comm m => SourcePos -> Text -> State FState -> m ([ProofText], State FState)
beginParsing pos text pState = do
  let tokens0 = case parserKind pState of
          Tex -> tokenize OutsideForthelEnv pos text
          NonTex -> tokenize TexDisabled pos text
  reportMeta $ mapMaybe reportComments tokens0
  let tokens = filter isProperToken tokens0
      st = State ((stUser pState) { tvrExpr = [] }) tokens (parserKind pState) pos
  continueParsing st

-- | Continue parsing after the parsing was suspended by a read instruction.
continueParsing :: Comm m => State FState -> m ([ProofText], State FState)
continueParsing st = case parserKind st of
  Tex -> launchParser texForthel st
  NonTex -> launchParser forthel st

-- | Run a given parser
launchParser :: Comm m => Parser st a -> State st -> m (a, State st)
launchParser parser state =
  case runP parser state of
    Error err -> errorParser (errorPos err) (show err)
    Ok [PR a st] -> return (a, st)