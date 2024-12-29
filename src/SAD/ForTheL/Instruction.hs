-- |
-- Module      : SAD.ForTheL.Instruction
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2018, Makarius Wenzel
-- License     : GPL-3
--
-- Syntax of ForThel Instructions.


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Instruction (
  instr,
  instrDrop,
  instrExit,
  instrRead
) where

import Control.Monad
import Control.Applicative ((<|>), some)
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import System.FilePath hiding ((</>))

import SAD.Data.Instr
import SAD.ForTheL.Base
import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.ForTheL.Reports
import SAD.Parser.Token

import Isabelle.Value qualified as Value
import Isabelle.Position qualified as Position
import Isabelle.Library

import Naproche.Param qualified as Param


instrPos :: (Position.T -> FTL ()) -> FTL a -> FTL (Position.T, a)
instrPos report p = do
  ((pos1, pos2), x) <- enclosed begin end p
  let pos = Position.range_position (pos1, Position.symbol_explode end pos2)
  report pos; return (pos, x)
  where begin = "["; end = "]"


instr :: FTL (Position.T, Instr)
instr =
  instrPos addDropReport $ readInstr >>=
    (\case
      GetRelativeFilePath _ -> fail "'read' not allowed here"
      Command Exit -> fail "'exit' and 'quit' not allowed here"
      i -> return i)


instrRead :: FTL (Position.T, Instr)
instrRead =
  instrPos addInstrReport $ readInstr >>=
    (\case
      i@(GetRelativeFilePath _) -> return i
      i@(GetModule _ _ _) -> return i
      _ -> mzero)

instrExit :: FTL (Position.T, Instr)
instrExit =
  instrPos addInstrReport $ readInstr >>=
    (\case
      i@(Command Exit) -> return i
      _ -> mzero)

instrDrop :: FTL (Position.T, Drop)
instrDrop = instrPos addInstrReport (token' "/" >> readInstrDrop)


readInstr :: FTL Instr
readInstr =
  readInstrCommand -|- readInstrLimit -|- readInstrBool -|- readInstrText -|- readInstrSynonym -|- readInstrModule
  where
    readInstrCommand = fmap Command (readKeywords keywordsCommand)
    readInstrSynonym = ap (readKeywords keywordsSynonym) readWords
    readInstrLimit = ap (readKeywords keywordsLimit) readInt
    readInstrBool = ap (readKeywords keywordsFlag) readBool
    readInstrText = ap (readKeywords keywordsArgument) readText
    readInstrModule = ap (readKeywords keywordsModule) readModule

readInt :: FTL Int
readInt = try $ do
  s <- readText
  maybe mzero return (Value.parse_nat $ make_bytes s)

readBool :: FTL Bool
readBool = try $ do
  s <- readText
  maybe mzero return (Param.parse_flag $ make_bytes s)

readText :: FTL Text
readText = fmap Text.concat readTexts


readTexts :: FTL [Text]
readTexts = texCommandWithArg "path" (chainLL1 notClosingBrc) <|> chainLL1 notClosingBrk
  where
    notClosingBrk = tokenPrim $ notCl "]"
    notClosingBrc = tokenPrim $ notCl "}"
    notCl str t = let tk = showToken t in guard (tk /= str) >> return tk

readModule :: FTL (FilePath, FilePath, String)
readModule = optInTexArg "path" $ do
  fstComp <- sepBy pathComponent (symbol "/")
  symbol "?"
  sndComp <- sepBy pathComponent (symbol "/")
  sep <- optLL1 False (symbol "?" >> return True)
  mdTrdComp <- if sep
    then Just <$> pathComponent
    else pure Nothing
  let modulePath = joinPath $ map Text.unpack fstComp
      archivePath = joinPath $ if sep then map Text.unpack sndComp else [""]
      moduleName = case mdTrdComp of Nothing -> Text.unpack (head sndComp); Just trdComp -> Text.unpack trdComp
  return (modulePath, archivePath, moduleName)
  where
    pathComponent = Text.concat <$> some (word <|> digit <|> getToken "-" <|> getToken "_" <|> getToken ".")


readWords :: FTL [Text]
readWords = shortHand </> chainLL1 word
  where
  shortHand = do
    w <- word ; root <- optLL1 w $ variant w; token "/"
    syms <- (fmap Text.toCaseFold word -|- variant w) `sepByLL1` token "/"
    return $ root : syms
  variant w = token "-" >> fmap (w <>) word

readInstrDrop :: FTL Drop
readInstrDrop = readInstrLimit -|- readInstrBool
  where
    readInstrLimit = readKeywords keywordsDropLimit
    readInstrBool = readKeywords keywordsDropFlag

-- | Try to parse the next token as one of the supplied keyword strings
-- and return the corresponding @a@ on success.
readKeywords :: [(a, Text)] -> FTL a
readKeywords keywords = try $ do
  s <- anyToken
  msum $ map (pure . fst) $ filter ((== s) . snd) keywords
