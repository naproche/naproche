{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Instruction datatype and core functions.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Instr where

import SAD.Core.SourcePos (SourcePos, SourceRange(..), noSourcePos, noRange)
import Data.Text (Text)


-- Position information

data Pos = Pos {start :: SourcePos, stop :: SourcePos, range :: SourceRange}
  deriving (Eq, Ord, Show)

position :: Pos -> SourcePos
position p = let SourceRange a _ = range p in a

noPos :: Pos
noPos = Pos noSourcePos noSourcePos noRange


-- | Indicate which of the parsers is currently used. This is must be recorded in the State
-- for read instruction to work properly.
data ParserKind = NonTex | Tex deriving (Eq, Ord, Show)

data Instr =
    Command Command
  | LimitBy Limit Int
  | SetFlag Flag Bool
  | GetArgument Argument Text
  | GetArguments Arguments [Text]
  deriving (Eq, Ord, Show)

data Drop =
    DropCommand Command
  | DropLimit Limit
  | DropFlag Flag
  | DropArgument Argument
  deriving (Eq, Ord, Show)


-- Instructions

data Command =
    EXIT     -- exit
  | QUIT     -- exit
  | THESIS   -- print current thesis
  | CONTEXT  -- print current context
  | FILTER   -- print simplified top-level context
  | RULES
  deriving (Eq, Ord, Show)

data Limit =
    Timelimit   -- time limit per prover launch  (3 sec)
  | Memorylimit -- memory limit per prover launch  (2048 MiB)
  deriving (Eq, Ord, Show)

data Flag =
    Prove          --  prove goals (yes)
  | Check          --  look for applicable definitions (yes)
  | CheckConsistency --  check that no contradictory axioms occur (yes)
  | Skipfail       --  ignore failed goals (no)
  | Printgoal      --  print current goal (yes)
  | Printprover    --  print the prover's logs (no)
  | Dump           --  print tasks in prover's syntax (no)
  | OnlyTranslate  --  translation only (comline only)
  | Help           --  print help (comline only)
  | Server         --  server mode (comline only)
  | UseTex         --  whether to use tex parser for the file passed in the CLI
  | UseFOF         --  whether to use FOF output
  deriving (Eq, Ord, Show)

data Argument =
    Init               --  init file (init.opt)
  | Text ParserKind    --  literal text
  | Read ParserKind    --  read file
  | Library            --  library directory
  | Provers            --  prover database
  | UseProver             --  current prover
  | ProverServerPort   --  port for prover server (on localhost)
  | ProverServerPassword  --  password for prover server
  deriving (Eq, Ord, Show)

data Arguments =
  Synonym
  deriving (Eq, Ord, Show)

-- Ask

askLimit :: Limit -> Int -> [Instr] -> Int
askLimit i d is  = head $ [ v | LimitBy j v <- is, i == j ] ++ [d]

askFlag :: Flag -> Bool -> [Instr] -> Bool
askFlag i d is  = head $ [ v | SetFlag j v <- is, i == j ] ++ [d]

askArgument :: Argument -> Text -> [Instr] -> Text
askArgument i d is  = head $ [ v | GetArgument j v <- is, i == j ] ++ [d]

-- Drop

-- | Drop an @Instr@ from the @[Instr]@ (assuming the latter doesn't contain duplicates)
dropInstr :: Drop -> [Instr] -> [Instr]
dropInstr (DropCommand m) (Command n : rs) | n == m = rs
dropInstr (DropLimit m) (LimitBy n _ : rs) | n == m = rs
dropInstr (DropFlag m) (SetFlag n _ : rs) | n == m = rs
dropInstr (DropArgument m) (GetArgument n _ : rs) | n == m = rs
dropInstr i (r : rs)  = r : dropInstr i rs
dropInstr _ _ = []


-- Keywords

keywordsCommand :: [(Command, Text)]
keywordsCommand =
 [(EXIT, "exit"),
  (QUIT, "quit"),
  (THESIS, "thesis"),
  (CONTEXT, "context"),
  (FILTER, "filter"),
  (RULES, "rules")]

keywordsLimit :: [(Limit, Text)]
keywordsLimit =
 [(Timelimit, "timelimit"),
  (Memorylimit, "memorylimit")]

keywordsFlag :: [(Flag, Text)]
keywordsFlag =
 [(Prove, "prove"),
  (Check, "check"),
  (CheckConsistency, "checkconsistency"),
  (Skipfail, "skipfail"),
  (Printgoal, "printgoal"),
  (Printprover, "printprover"),
  (Dump, "dump"),
  (UseTex, "tex"),
  (UseFOF, "fof")]

keywordsArgument :: [(Argument, Text)]
keywordsArgument =
 [(Read NonTex, "read"),
  (Read Tex, "readtex"),
  (Library, "library"),
  (Provers, "provers"),
  (UseProver, "prover")]

keywordsArguments :: [(Arguments, Text)]
keywordsArguments =
  [(Synonym, "synonym")]

-- distinguish between parser and verifier instructions

isParserInstruction :: Instr -> Bool
isParserInstruction i = case i of
  Command EXIT -> True
  Command QUIT -> True
  GetArgument (Read _) _ -> True
  GetArguments Synonym _ -> True
  _ -> False
