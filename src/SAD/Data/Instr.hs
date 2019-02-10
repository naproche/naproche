{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Instruction datatype and core functions.
-}

module SAD.Data.Instr where

import Prelude hiding (Int, Bool, String, drop)
import qualified Prelude
import Control.Monad
import SAD.Core.SourcePos (SourcePos, SourceRange)
import qualified SAD.Core.SourcePos as SourcePos


-- Position information

data Pos = Pos {start :: SourcePos, stop :: SourcePos, range :: SourceRange}

position :: Pos -> SourcePos
position = fst . range

noPos :: Pos
noPos = Pos SourcePos.noPos SourcePos.noPos SourcePos.noRange


-- Instruction types

data Instr =
    Command Command
  | Int Int Prelude.Int
  | Bool Bool Prelude.Bool
  | String String Prelude.String
  | Strings Strings [Prelude.String]
  deriving (Show, Eq)

data Drop =
    DropCommand Command
  | DropInt Int
  | DropBool Bool
  | DropString String
  deriving (Show, Eq)


-- Instructions

data Command =
    EXIT     -- exit
  | QUIT     -- exit
  | THESIS   -- print current thesis
  | CONTEXT  -- print current context
  | FILTER   -- print simplified top-level context
  | RULES
  deriving (Eq,Show)

data Int =
    Timelimit   -- time limit per prover launch  (3 sec)
  | Depthlimit  -- number of reasoner iterations (7)
  | Checktime   -- time limit for checker's tasks (1 sec)
  | Checkdepth  -- depth limit for checker's tasks (3)
  deriving (Eq,Show)

data Bool =
    Prove          --  prove goals (yes)
  | Check          --  look for applicable definitions (yes)
  | Symsign        --  rename symbols with diverging defs (yes)
  | Info           --  accumulate evidences (yes)
  | Thesis         --  modify thesis (yes)
  | Filter         --  simplify the context (yes)
  | Skipfail       --  ignore failed goals (no)
  | Flat           --  do not descend into proofs (no)
  | Printgoal      --  print current goal (yes)
  | Printreason    --  print reasoner's log (no)
  | Printsection   --  print current sentence (no)
  | Printcheck     --  print definition checks (no)
  | Printprover    --  print prover's log (no)
  | Printunfold    --  print definition unfolds (no)
  | Printfulltask  --  print inference tasks (no)
  | Dump           --  print tasks in prover's syntax (no)
  | OnlyTranslate  --  translation only (comline only)
  | Verbose        --  verbosity control (comline only)
  | Help           --  print help (comline only)
  | Server         --  server mode (comline only)
  | Printsimp      --  print simplifier log (no)
  | Printthesis    --  print thesis development (no)
  | Ontored        --  use ontological reduction (no)
  | Unfold         --  general unfolding (on)
  | Unfoldsf       --  general unfolding of sets and functions
  | Unfoldlow      --  unfold the whole low level context (yes)
  | Unfoldlowsf    --  unfold set and function conditions in low level (no)
  | Checkontored   --  enable ontological reduction for checks (off)
  | Translation    --  print first-order translation of sentences
  deriving (Eq,Show)

data String =
    Init     --  init file (init.opt)
  | Text     --  literal text
  | File     --  read file
  | Read     --  read library file
  | Library  --  library directory
  | Provers  --  prover database
  | Prover   --  current prover
  deriving (Eq,Show)

data Strings =
  Synonym
  deriving (Eq,Show)

-- Ask

askInt :: Int -> Prelude.Int -> [Instr] -> Prelude.Int
askInt i d is  = head $ [ v | Int j v <- is, i == j ] ++ [d]

askBool :: Bool -> Prelude.Bool -> [Instr] -> Prelude.Bool
askBool i d is  = head $ [ v | Bool j v <- is, i == j ] ++ [d]

askString :: String -> Prelude.String -> [Instr] -> Prelude.String
askString i d is  = head $ [ v | String j v <- is, i == j ] ++ [d]


-- Drop

drop :: Drop -> [Instr] -> [Instr]
drop (DropCommand m) (Command n : rs) | n == m = rs
drop (DropInt m) (Int n _ : rs) | n == m = rs
drop (DropBool m) (Bool n _ : rs) | n == m = rs
drop (DropString m) (String n _ : rs) | n == m = rs
drop i (r : rs)  = r : drop i rs
drop _ _ = []


-- Keywords

keywordsCommand :: [(Command, Prelude.String)]
keywordsCommand =
 [(EXIT, "exit"),
  (QUIT, "quit"),
  (THESIS, "thesis"),
  (CONTEXT, "context"),
  (FILTER, "filter"),
  (RULES, "rules")]

keywordsInt :: [(Int, Prelude.String)]
keywordsInt =
 [(Timelimit, "timelimit"),
  (Depthlimit, "depthlimit"),
  (Checktime, "checktime"),
  (Checkdepth, "checkdepth")]

keywordsBool :: [(Bool, Prelude.String)]
keywordsBool =
 [(Prove, "prove"),
  (Check, "check"),
  (Symsign, "symsign"),
  (Info, "info"),
  (Thesis, "thesis"),
  (Filter, "filter"),
  (Skipfail, "skipfail"),
  (Flat, "flat"),
  (Printgoal, "printgoal"),
  (Printsection, "printsection"),
  (Printcheck, "printcheck"),
  (Printunfold, "printunfold"),
  (Printreason, "printreason"),
  (Printprover, "printprover"),
  (Printfulltask, "printfulltask"),
  (Dump, "dump"),
  (Printsimp, "printsimp"),
  (Printthesis, "printthesis"),
  (Ontored, "ontored"),
  (Unfold, "unfold"),
  (Unfoldsf, "unfoldsf"),
  (Unfoldlow, "unfoldlow"),
  (Unfoldlowsf, "unfoldlowsf"),
  (Checkontored, "checkontored"),
  (Translation, "translation")]

keywordsString :: [(String, Prelude.String)]
keywordsString =
 [(Read, "read"),
  (Library, "library"),
  (Provers, "provers"),
  (Prover, "prover")]

keywordsStrings :: [(Strings, Prelude.String)]
keywordsStrings =
  [(Synonym, "synonym")]

-- distiguish between parser and verifier instructions 

isParserInstruction :: Instr -> Prelude.Bool
isParserInstruction i = case i of
  Command EXIT -> True; Command QUIT -> True; String Read _ -> True;
  Strings Synonym _ -> True; _ -> False