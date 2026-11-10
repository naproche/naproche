{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.ForTheL.Instruction
-- Description : Syntax of ForThel Instructions.
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2018, Makarius Wenzel
-- License     : GPL-3
module SAD.ForTheL.Instruction (
  instr,
  instrDrop,
  instrExit,
  instrRead
) where

import Control.Applicative ((<|>))
import Control.Monad

import Data.Text (Text)
import Data.Text qualified as Text

import Isabelle.Bytes (Bytes)
import Isabelle.Bytes qualified as Bytes
import Isabelle.Library
import Isabelle.Position qualified as Position
import Isabelle.Value qualified as Value

import Naproche.Param qualified as Param

import SAD.Data.Instr
import SAD.ForTheL.Base
import SAD.ForTheL.Reports
import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.Parser.Token


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
      Command Exit -> fail "'exit' not allowed here"
      i -> return i)


instrRead :: FTL (Position.T, Instr)
instrRead =
  instrPos addInstrReport $ readInstr >>=
    (\case
      i@(GetRelativeFilePath _) -> return i
      i@(GetModule {}) -> return i
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
  readInstrCommand -|- readInstrLimit -|- readInstrBool -|- readInstrText -|- readInstrPath -|- readInstrSynonym
  where
    readInstrCommand = fmap Command (readKeywords keywordsCommand)
    readInstrSynonym = ap (readKeywords keywordsSynonym) readWords
    readInstrLimit = ap (readKeywords keywordsLimit) readInt
    readInstrBool = ap (readKeywords keywordsFlag) readBool
    readInstrText = ap (readKeywords keywordsText) readBytes
    readInstrPath = ap (readKeywords keywordsPath) readPath

readInt :: FTL Int
readInt = try $ do
  s <- readBytes
  maybe mzero return (Value.parse_nat s)

readBool :: FTL Bool
readBool = try $ do
  s <- readBytes
  maybe mzero return (Param.parse_flag s)

readPath :: FTL FilePath
readPath = make_string <$> readBytes

readBytes :: FTL Bytes
readBytes = Bytes.concat . map make_bytes <$> (texCommandWithArg "path" (chainLL1 notClosingBrc) <|> chainLL1 notClosingBrk)
  where
    notClosingBrk = tokenPrim $ notCl "]"
    notClosingBrc = tokenPrim $ notCl "}"
    notCl str t = let tk = tokenText t in guard (tk /= str) >> return tk


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
readKeywords :: [(a, Bytes)] -> FTL a
readKeywords keywords = try $ do
  s <- make_bytes <$> anyToken
  msum $ map (pure . fst) $ filter ((== s) . snd) keywords
