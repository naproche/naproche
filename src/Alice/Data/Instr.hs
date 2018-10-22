{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Instruction datatype and core functions.
-}

module Alice.Data.Instr where

import Control.Monad

data Instr  = InCom InCom           -- Instruction Command
            | InInt InInt Int       -- Instruction Integer
            | InBin InBin Bool      -- Instruction Binary
            | InStr InStr String    -- Instruction String
            | InPar InPar [String]  -- Instruction with multiple parameters
            deriving Show

{- drop type for command, integer, binary and string instruction types -}
data Idrop  = IdCom InCom
            | IdInt InInt
            | IdBin InBin
            | IdStr InStr
            deriving Show


-- Instructions

data InCom  = ICexit  --  exit
            | ICPths  --  print current thesis
            | ICPcnt  --  print current context
            | ICPflt  --  print simplified top-level context
            | ICRuls
            deriving (Eq,Show)

data InInt  = IItlim  --  time limit per prover launch  (3 sec)
            | IIdpth  --  number of reasoner iterations (7)
            | IIchtl  --  time limit for checker's tasks (1 sec)
            | IIchdp  --  depth limit for checker's tasks (3)
            deriving (Eq,Show)

data InBin  = IBprov  --  prove goals (yes)
            | IBchck  --  look for applicable definitions (yes)
            | IBsign  --  rename symbols with diverging defs (yes)
            | IBinfo  --  accumulate evidences (yes)
            | IBthes  --  modify thesis (yes)
            | IBfilt  --  simplify the context (yes)
            | IBskip  --  ignore failed goals (no)
            | IBflat  --  do not descend into proofs (no)
            | IBPgls  --  print current goal (yes)
            | IBPrsn  --  print reasoner's log (no)
            | IBPsct  --  print current sentence (no)
            | IBPchk  --  print definition checks (no)
            | IBPprv  --  print prover's log (no)
            | IBPunf  --  print definition unfolds (no)
            | IBPtsk  --  print inference tasks (no)
            | IBPdmp  --  print tasks in prover's syntax (no)
            | IBtext  --  translation only (comline only)
            | IBverb  --  verbosity control (comline only)
            | IBhelp  --  print help (comline only)
            | IBPsmp  --  print simplifier log (no)
            | IBPths  --  print thesis development (no)
            | IBOnto  --  use ontological reduction (no)
            | IBUnfl  --  general unfolding (on)
            | IBUnfs  --  general unfolding of sets and functions
            | IBUfdl  --  unfold the whole low level context (yes)
            | IBUfds  --  unfold set and function conditions in low level (no)
            | IBOnch  --  enable ontological reduction for checks (off)
            | IBPIDE  --  enable PIDE protocol (off)
            deriving (Eq,Show)

data InStr  = ISinit  --  init file (init.opt)
            | ISfile  --  read file
            | ISread  --  read library file
            | ISlibr  --  library directory
            | ISprdb  --  prover database
            | ISprvr  --  current prover
            deriving (Eq,Show)

data InPar = IPgrup   -- form a group of identifiers
           | IPscnt   -- set the context
           | IPdcnt   -- drop a section from the context
           | IPacnt   -- add a section to the context
           deriving (Eq,Show)


-- Ask functions

askII :: InInt -> Int -> [Instr] -> Int
askII i d is  = head $ [ v | InInt j v <- is, i == j ] ++ [d]

askIB :: InBin -> Bool -> [Instr] -> Bool
askIB i d is  = head $ [ v | InBin j v <- is, i == j ] ++ [d]

askIS :: InStr -> String -> [Instr] -> String
askIS i d is  = head $ [ v | InStr j v <- is, i == j ] ++ [d]

dropI :: Idrop -> [Instr] -> [Instr]
dropI (IdCom m) (InCom n   : rs) | n == m = rs
dropI (IdInt m) (InInt n _ : rs) | n == m = rs
dropI (IdBin m) (InBin n _ : rs) | n == m = rs
dropI (IdStr m) (InStr n _ : rs) | n == m = rs
dropI i (r : rs)  = r : dropI i rs
dropI _ _ = []


-- Keywords

setIC :: [(InCom, [String])]
setIC = [ (ICexit,  ["exit", "quit"]),
          (ICPths,  ["thesis"]),
          (ICPcnt,  ["context"]),
          (ICPflt,  ["filter"]),
          (ICRuls,  ["rules"]) ]

setII :: [(InInt, [String])]
setII = [ (IItlim,  ["timelimit"]),
          (IIdpth,  ["depthlimit"]),
          (IIchtl,  ["checktime"]),
          (IIchdp,  ["checkdepth"]) ]

setIB :: [(InBin, [String])]
setIB = [ (IBprov,  ["prove"]),
          (IBchck,  ["check"]),
          (IBsign,  ["symsign"]),
          (IBinfo,  ["info"]),
          (IBthes,  ["thesis"]),
          (IBfilt,  ["filter"]),
          (IBskip,  ["skipfail"]),
          (IBflat,  ["flat"]),
          (IBPgls,  ["printgoal"]),
          (IBPsct,  ["printsection"]),
          (IBPchk,  ["printcheck"]),
          (IBPunf,  ["printunfold"]),
          (IBPrsn,  ["printreason"]),
          (IBPprv,  ["printprover"]),
          (IBPtsk,  ["printfulltask"]),
          (IBPdmp,  ["dump"]),
          (IBPsmp,  ["printsimp"]),
          (IBPths,  ["printthesis"]),
          (IBOnto,  ["ontored"]),
          (IBUnfl,  ["unfold"]),
          (IBUnfs,  ["unfoldsf"]),
          (IBUfdl,  ["unfoldlow"]),
          (IBUfds,  ["unfoldlowsf"]),
          (IBOnch,  ["checkontored"]),
          (IBPIDE,  ["PIDE"])]

setIS :: [(InStr, [String])]
setIS = [ (ISread,  ["read"]),
          (ISlibr,  ["library"]),
          (ISprdb,  ["provers"]),
          (ISprvr,  ["prover"]) ]

setIP = [ (IPgrup, ["group"]),
          (IPscnt, ["setCtxt"]),
          (IPdcnt, ["drpCtxt"]),
          (IPacnt, ["addCtxt"])]

relevant (InPar IPscnt _) = True
relevant _ = False
