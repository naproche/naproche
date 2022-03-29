{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Syntax of ForThel Instructions.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Instruction
  ( instr
  , instrDrop
  , instrExit
  , instrRead
  ) where

import Control.Monad
import Control.Applicative ((<|>))
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

import SAD.Data.Instr

import SAD.ForTheL.Base

import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.ForTheL.Reports
import SAD.Parser.Token
import qualified Naproche.Param as Param

import qualified Isabelle.Value as Value
import qualified Isabelle.Position as Position
import Isabelle.Library


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
      GetArgument (Read _) _ -> fail "'read' and 'readtex' not allowed here"
      Command Exit -> fail "'exit' and 'quit' not allowed here"
      i -> return i)


instrRead :: FTL (Position.T, Instr)
instrRead =
  instrPos addInstrReport $ readInstr >>=
    (\case
      i@(GetArgument (Read _) _) -> return i
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
  readInstrCommand -|- readInstrLimit -|- readInstrBool -|- readInstrText -|- readInstrSynonym
  where
    readInstrCommand = fmap Command (readKeywords keywordsCommand)
    readInstrSynonym = ap (readKeywords keywordsSynonym) readWords
    readInstrLimit = ap (readKeywords keywordsLimit) readInt
    readInstrBool = ap (readKeywords keywordsFlag) readBool
    readInstrText = ap (readKeywords keywordsArgument) readText

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
readTexts = texEnclosed "path" (chainLL1 notClosingBrc) <|> chainLL1 notClosingBrk
  where
    notClosingBrk = tokenPrim $ notCl "]"
    notClosingBrc = tokenPrim $ notCl "}"
    notCl str t = let tk = showToken t in guard (tk /= str) >> return tk

readWords :: FTL [Text]
readWords = shortHand </> chainLL1 word
  where
  shortHand = do
    w <- word ; root <- optLL1 w $ variant w; token "/"
    syms <- (fmap Text.toCaseFold word -|- variant w) `sepByLL1` token "/"
    return $ root : syms
  variant w = token "-" >> fmap (w <>) word

readInstrDrop :: FTL Drop
readInstrDrop = readInstrCommand -|- readInstrLimit -|- readInstrBool
  where
    readInstrCommand = fmap DropCommand (readKeywords keywordsCommand)
    readInstrLimit = readKeywords keywordsDropLimit
    readInstrBool = readKeywords keywordsDropFlag

-- | Try to parse the next token as one of the supplied keyword strings
-- and return the corresponding @a@ on success.
readKeywords :: [(a, Text)] -> FTL a
readKeywords keywords = try $ do
  s <- anyToken
  msum $ map (pure . fst) $ filter ((== s) . snd) keywords
