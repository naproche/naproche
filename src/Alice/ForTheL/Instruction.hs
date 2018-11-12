{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Syntax of ForThel Instructions.
-}

module Alice.ForTheL.Instruction where

import Control.Monad

import Alice.Data.Instr (Instr, Idrop)
import qualified Alice.Data.Instr as Instr

import Alice.Parser.Base
import Alice.Parser.Combinators
import Alice.Parser.Primitives

import Alice.Parser.Token

instr :: Parser st Instr
instr = exbrk (readInstr >>= gut)
  where
    gut (Instr.InStr Instr.ISread _)  = fail "'read' not allowed here"
    gut (Instr.InCom Instr.ICexit)    = fail "'exit'/'quit' not allowed here"
    gut i = return i


iRead :: Parser st Instr
iRead = exbrk (readInstr >>= gut)
  where
    gut i@(Instr.InStr Instr.ISread _)  = return i
    gut _ = mzero


iExit :: Parser st ()
iExit = exbrk (readInstr >>= gut)
  where
    gut (Instr.InCom Instr.ICexit)  = return ()
    gut _ = mzero

iDrop :: Parser st Idrop
iDrop = exbrk (wdToken "/" >> readInstrDrop)


readInstr :: Parser st Instr
readInstr = readIC -|- readII -|- readIB -|- readIS -|- readIP
  where
    readIC = fmap Instr.InCom (readIX Instr.setIC)
    readII = liftM2 Instr.InInt (readIX Instr.setII) readInt
    readIB = liftM2 Instr.InBin (readIX Instr.setIB) readBin
    readIS = liftM2 Instr.InStr (readIX Instr.setIS) readStr
    readIP = liftM2 Instr.InPar (readIX Instr.setIP) readPar

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

readStr = fmap concat readPar


readPar = chainLL1 notClosingBrk
  where
    notClosingBrk = tokenPrim notCl
    notCl t = let tk = showToken t in guard (tk /= "]") >> return tk


readInstrDrop :: Parser st Idrop
readInstrDrop = readIC -|- readII -|- readIB -|- readIS
  where
    readIC  = fmap Instr.IdCom (readIX Instr.setIC)
    readII  = fmap Instr.IdInt (readIX Instr.setII)
    readIB  = fmap Instr.IdBin (readIX Instr.setIB)
    readIS  = fmap Instr.IdStr (readIX Instr.setIS)


readIX :: [(a, [String])] -> Parser st a
readIX ix = try $
  anyToken >>= \s -> msum . map (return . fst) $ filter (elem s . snd) ix
