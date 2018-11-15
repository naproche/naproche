{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius (2018)

Syntax of ForThel Instructions.
-}

module SAD.ForTheL.Instruction where

import Control.Monad

import SAD.Core.SourcePos
import SAD.Data.Instr (Instr)
import qualified SAD.Data.Instr as Instr

import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Parser.Primitives

import SAD.Parser.Token


instr :: Parser st (SourceRange, Instr)
instr = exbrkRange (readInstr >>= gut)
  where
    gut (Instr.String Instr.Read _) = fail "'read' not allowed here"
    gut (Instr.Command Instr.EXIT) = fail "'exit' not allowed here"
    gut (Instr.Command Instr.QUIT) = fail "'quit' not allowed here"
    gut i = return i


instrRead :: Parser st (SourceRange, Instr)
instrRead = exbrkRange (readInstr >>= gut)
  where
    gut i@(Instr.String Instr.Read _) = return i
    gut _ = mzero


instrExit :: Parser st ()
instrExit = exbrk (readInstr >>= gut)
  where
    gut (Instr.Command Instr.EXIT) = return ()
    gut (Instr.Command Instr.QUIT) = return ()
    gut _ = mzero

instrDrop :: Parser st (SourceRange, Instr.Drop)
instrDrop = exbrkRange (wdToken "/" >> readInstrDrop)


readInstr :: Parser st Instr
readInstr =
  readInstrCommand -|- readInstrInt -|- readInstrBool -|- readInstrString -|- readInstrStrings
  where
    readInstrCommand = fmap Instr.Command (readKeywords Instr.keywordsCommand)
    readInstrInt = liftM2 Instr.Int (readKeywords Instr.keywordsInt) readInt
    readInstrBool = liftM2 Instr.Bool (readKeywords Instr.keywordsBool) readBool
    readInstrString = liftM2 Instr.String (readKeywords Instr.keywordsString) readString
    readInstrStrings = liftM2 Instr.Strings (readKeywords Instr.keywordsStrings) readStrings

readInt = try $ readString >>= intCheck
  where
    intCheck s = case reads s of
      ((n,[]):_) | n >= 0 -> return n
      _                   -> mzero

readBool = try $ readString >>= boolCheck
  where
    boolCheck "yes" = return True
    boolCheck "on"  = return True
    boolCheck "no"  = return False
    boolCheck "off" = return False
    boolCheck _     = mzero

readString = fmap concat readStrings


readStrings = chainLL1 notClosingBrk
  where
    notClosingBrk = tokenPrim notCl
    notCl t = let tk = showToken t in guard (tk /= "]") >> return tk


readInstrDrop :: Parser st Instr.Drop
readInstrDrop = readInstrCommand -|- readInstrInt -|- readInstrBool -|- readInstrString
  where
    readInstrCommand = fmap Instr.DropCommand (readKeywords Instr.keywordsCommand)
    readInstrInt = fmap Instr.DropInt (readKeywords Instr.keywordsInt)
    readInstrBool = fmap Instr.DropBool (readKeywords Instr.keywordsBool)
    readInstrString = fmap Instr.DropString (readKeywords Instr.keywordsString)


readKeywords :: [(a, String)] -> Parser st a
readKeywords keywords = try $
  anyToken >>= \s -> msum . map (return . fst) $ filter ((== s) . snd) keywords
