{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Syntax of ForThel Instructions.
-}



module Alice.ForTheL.Instruction where

import Control.Monad

import Alice.Data.Instr

import Alice.Parser.Base
import Alice.Parser.Combinators
import Alice.Parser.Primitives

import Alice.Parser.Token

instr :: Parser st Instr
instr = exbrk (readInstr >>= gut)
  where
    gut (InStr ISread _)  = fail "'read' not allowed here"
    gut (InCom ICexit)    = fail "'exit'/'quit' not allowed here"
    gut i = return i


iRead :: Parser st Instr
iRead = exbrk (readInstr >>= gut)
  where
    gut i@(InStr ISread _)  = return i
    gut _ = mzero


iExit :: Parser st ()
iExit = exbrk (readInstr >>= gut)
  where
    gut (InCom ICexit)  = return ()
    gut _ = mzero

iDrop :: Parser st Idrop
iDrop = exbrk (wd_token "/" >> readInstrDrop)


readInstr :: Parser st Instr
readInstr = readIC -|- readII -|- readIB -|- readIS -|- readIP
  where
    readIC = liftM  InCom (readIX setIC)
    readII = liftM2 InInt (readIX setII) readInt
    readIB = liftM2 InBin (readIX setIB) readBin
    readIS = liftM2 InStr (readIX setIS) readStr
    readIP = liftM2 InPar (readIX setIP) readPar

readInt = try $ readStr >>= intCheck
  where
    intCheck s = case reads s of
      ((n,[]):_) | n >= 0 -> return n
      _                   -> mzero

readBin = try $ readStr >>= binCheck
  where
    binCheck "yes" = return True
    binCheck "on"  = return True
    binCheck "no"  = return False
    binCheck "off" = return False
    binCheck _     = mzero

readStr = liftM concat readPar


readPar = chainLL1 notClosingBrk
  where
    notClosingBrk = tokenPrim notCl
    notCl t = let tk = showToken t in guard (tk /= "]") >> return tk


readInstrDrop :: Parser st Idrop
readInstrDrop = readIC -|- readII -|- readIB -|- readIS
  where
    readIC  = liftM IdCom (readIX setIC)
    readII  = liftM IdInt (readIX setII)
    readIB  = liftM IdBin (readIX setIB)
    readIS  = liftM IdStr (readIX setIS)


readIX :: [(a, [String])] -> Parser st a
readIX ix = try $
  anyToken >>= \s -> msum . map (return . fst) $ filter (elem s . snd) ix
