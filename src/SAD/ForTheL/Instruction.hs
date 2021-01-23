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
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

import SAD.Core.SourcePos
import SAD.Data.Instr

import SAD.ForTheL.Base

import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.ForTheL.Reports
import SAD.Parser.Token


instrPos :: (Pos -> FTL ()) -> FTL a -> FTL (Pos, a)
instrPos report p = do
  ((pos1, pos2), x) <- enclosed begin end p
  let pos = Pos pos1 pos2 (makeRange (pos1, pos2 `advancePos` end))
  report pos; return (pos, x)
  where begin = "["; end = "]"


instr :: FTL (Pos, Instr)
instr =
  instrPos addDropReport $ readInstr >>=
    (\case
      GetArgument (Read _) _ -> fail "'read' and 'readtex' not allowed here"
      Command EXIT -> fail "'exit' not allowed here"
      Command QUIT -> fail "'quit' not allowed here"
      i -> return i)


instrRead :: FTL (Pos, Instr)
instrRead =
  instrPos addInstrReport $ readInstr >>=
    (\case
      i@(GetArgument (Read _) _) -> return i
      _ -> mzero)

instrExit :: FTL (Pos, Instr)
instrExit =
  instrPos addInstrReport $ readInstr >>=
    (\case
      i@(Command EXIT) -> return i
      i@(Command QUIT) -> return i
      _ -> mzero)

instrDrop :: FTL (Pos, Drop)
instrDrop = instrPos addInstrReport (token' "/" >> readInstrDrop)


readInstr :: FTL Instr
readInstr =
  readInstrCommand -|- readInstrLimit -|- readInstrBool -|- readInstrText -|- readInstrTexts
  where
    readInstrCommand = fmap Command (readKeywords keywordsCommand)
    readInstrLimit = liftM2 LimitBy (readKeywords keywordsLimit) readInt
    readInstrBool = liftM2 SetFlag (readKeywords keywordsFlag) readBool
    readInstrText = liftM2 GetArgument (readKeywords keywordsArgument) readText
    readInstrTexts = liftM2 GetArguments (readKeywords keywordsArguments) readWords

readInt :: FTL Int
readInt = try $ readText >>= intCheck
  where
    intCheck s = case reads $ Text.unpack s of
      ((n,[]):_) | n >= 0 -> return n
      _                   -> mzero

readBool :: FTL Bool
readBool = try $ readText >>= boolCheck
  where
    boolCheck "yes" = return True
    boolCheck "on"  = return True
    boolCheck "no"  = return False
    boolCheck "off" = return False
    boolCheck _     = mzero

readText :: FTL Text
readText = fmap Text.concat readTexts


readTexts :: FTL [Text]
readTexts = chainLL1 notClosingBrk
  where
    notClosingBrk = tokenPrim notCl
    notCl t = let tk = showToken t in guard (tk /= "]") >> return tk

readWords :: FTL [Text]
readWords = shortHand </> chainLL1 word
  where
  shortHand = do
    w <- word ; root <- optLL1 w $ variant w; token "/"
    syms <- (fmap (Text.toCaseFold) word -|- variant w) `sepByLL1` token "/"
    return $ root : syms
  variant w = token "-" >> fmap (w <>) word

readInstrDrop :: FTL Drop
readInstrDrop = readInstrCommand -|- readInstrLimit -|- readInstrBool
  where
    readInstrCommand = fmap DropCommand (readKeywords keywordsCommand)
    readInstrLimit = fmap DropLimit (readKeywords keywordsLimit)
    readInstrBool = fmap DropFlag (readKeywords keywordsFlag)

-- | Try to parse the next token as one of the supplied keyword strings
-- and return the corresponding @a@ on success.
readKeywords :: [(a, Text)] -> FTL a
readKeywords keywords = try $ do
  s <- anyToken
  msum $ map (pure . fst) $ filter ((== s) . snd) keywords
