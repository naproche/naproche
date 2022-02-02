{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018, 2022)

Instruction datatype and core functions.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Instr
  (UnderlyingTheory(..), ParserKind(..), Instr(..), Drop(..), Command(..), Argument(..),
  askParam, askArgument, askTheory, dropInstr,
  timelimitParam, memorylimitParam, depthlimitParam, checktimeParam, checkdepthParam,
  proveParam, checkParam, checkconsistencyParam, symsignParam, infoParam, thesisParam,
  filterParam, skipfailParam, flatParam, printgoalParam, printsectionParam, printcheckParam,
  printunfoldParam, printreasonParam, printproverParam, printfulltaskParam, dumpParam,
  printsimpParam, printthesisParam, unfoldParam, unfoldsfParam, unfoldlowParam, unfoldlowsfParam,
  translationParam, texParam,
  helpParam, serverParam, onlytranslateParam,
  keywordsCommand, keywordsSynonym, keywordsLimit, keywordsFlag, keywordsArgument,
  keywordsDropLimit, keywordsDropFlag, isParserInstruction)
where

import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Lazy
import Isabelle.Bytes (Bytes)
import Isabelle.Library

import qualified Naproche.Param as Param


-- Instruction types

data UnderlyingTheory = FirstOrderLogic | CiC | Lean
  deriving (Eq, Ord, Show)

-- | Indicate which of the parsers is currently used. This is must be recorded in the State
-- for read instruction to work properly.
data ParserKind = NonTex | Tex deriving (Eq, Ord, Show)

data Instr =
    Command Command
  | Synonym [Text]
  | SetBool (Param.T Bool) Bool
  | SetInt (Param.T Int) Int
  | SetBytes (Param.T Bytes) Bytes
  | GetArgument Argument Text
  | Theory UnderlyingTheory
  | Verbose Bool
  deriving (Eq, Ord, Show)

data Drop =
    DropCommand Command
  | DropBool (Param.T Bool)
  | DropInt (Param.T Int)
  | DropBytes (Param.T Bytes)
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

data Argument =
    Init               --  init file (init.opt)
  | Text ParserKind    --  literal text
  | File ParserKind    --  read file
  | Read ParserKind    --  read library file
  | Library            --  library directory
  | Prover             --  current prover
  deriving (Eq, Ord, Show)


-- Ask

askParam :: Param.T a -> [Instr] -> a
askParam p = Param.get p . foldr instr allParams
  where
    instr :: Instr -> Param.Env -> Param.Env
    instr (SetBool p x) = Param.put p x
    instr (SetInt p x) = Param.put p x
    instr (SetBytes p x) = Param.put p (make_bytes x)
    instr (Verbose False) =
      Param.put printgoalParam False .
      Param.put printreasonParam False .
      Param.put printsectionParam False .
      Param.put printcheckParam False .
      Param.put printproverParam False .
      Param.put printunfoldParam False .
      Param.put printfulltaskParam False
    instr (Verbose True) =
      Param.put printgoalParam True .
      Param.put printreasonParam True .
      Param.put printcheckParam True .
      Param.put printproverParam True .
      Param.put printunfoldParam True .
      Param.put printfulltaskParam True
    instr _ = id

askArgument :: Argument -> Text -> [Instr] -> Text
askArgument i d is  = head $ [ v | GetArgument j v <- is, i == j ] ++ [d]

askTheory :: UnderlyingTheory -> [Instr] -> UnderlyingTheory
askTheory d is = head $ [ t | Theory t <- is] ++ [d]

-- Drop

-- | Drop an @Instr@ from the @[Instr]@ (assuming the latter doesn't contain duplicates)
dropInstr :: Drop -> [Instr] -> [Instr]
dropInstr (DropCommand m) (Command n : rs) | n == m = rs
dropInstr (DropBool p) (SetBool p' _ : rs) | p == p' = rs
dropInstr (DropInt p) (SetInt p' _ : rs) | p == p' = rs
dropInstr (DropBytes p) (SetBytes p' _ : rs) | p == p' = rs
dropInstr (DropArgument m) (GetArgument n _ : rs) | n == m = rs
dropInstr i (r : rs)  = r : dropInstr i rs
dropInstr _ _ = []


-- Parameters

allParams :: Param.Env
allParams = foldr Param.declare (foldr Param.declare Param.empty allLimits) allFlags
  where allLimits = textLimits; allFlags = textFlags ++ programFlags

textLimits :: [Param.T Int]
timelimitParam, memorylimitParam, depthlimitParam, checktimeParam, checkdepthParam :: Param.T Int
textLimits @ [timelimitParam, memorylimitParam, depthlimitParam, checktimeParam, checkdepthParam] =
  [Param.nat "timelimit" "N seconds per prover call" 3,
   Param.nat "memorylimit" "maximum N MiB of memory usage per prover call" 2048,
   Param.nat "depthlimit" "N reasoner loops per goal" 7,
   Param.nat "checktime" "timelimit for checker's tasks" 1,
   Param.nat "checkdepth" "depthlimit for checker's tasks" 3]

textFlags :: [Param.T Bool]
proveParam, checkParam, checkconsistencyParam, symsignParam, infoParam, thesisParam,
  filterParam, skipfailParam, flatParam, printgoalParam, printsectionParam, printcheckParam,
  printunfoldParam, printreasonParam, printproverParam, printfulltaskParam, dumpParam,
  printsimpParam, printthesisParam, unfoldParam, unfoldsfParam, unfoldlowParam, unfoldlowsfParam,
  translationParam, texParam :: Param.T Bool
textFlags @ [proveParam, checkParam, checkconsistencyParam, symsignParam, infoParam, thesisParam,
  filterParam, skipfailParam, flatParam, printgoalParam, printsectionParam, printcheckParam,
  printunfoldParam, printreasonParam, printproverParam, printfulltaskParam, dumpParam,
  printsimpParam, printthesisParam, unfoldParam, unfoldsfParam, unfoldlowParam, unfoldlowsfParam,
  translationParam, texParam] =
   [Param.flag "prove" "prove goals in the text" True,
    Param.flag "check" "check symbols for definedness" True,
    Param.flag "checkconsistency" "check that no contradictory axioms occur" True,
    Param.flag "symsign" "prevent ill-typed unification" True,
    Param.flag "info" "collect \"evidence\" literals" True,
    Param.flag "thesis" "maintain current thesis" True,
    Param.flag "filter" "filter prover tasks" True,
    Param.flag "skipfail" "ignore failed goals" False,
    Param.flag "flat" "do not read proofs" False,
    Param.flag "printgoal" "print current goal" True,
    Param.flag "printsection" "print sentence translations" False,
    Param.flag "printcheck" "print checker's messages" False,
    Param.flag "printunfold" "print definition unfoldings" False,
    Param.flag "printreason" "print reasoner's messages" False,
    Param.flag "printprover" "print prover's messages" False,
    Param.flag "printfulltask" "print full prover tasks" False,
    Param.flag "dump" "print tasks in prover's syntax" False,
    Param.flag "printsimp" "print simplification process" False,
    Param.flag "printthesis" "print thesis development" False,
    Param.flag "unfold" "enable unfolding of definitions" True,
    Param.flag "unfoldsf" "enable unfolding of class conditions and map evaluations" True,
    Param.flag "unfoldlow" "enable unfolding of definitions in the whole low level context" True,
    Param.flag "unfoldlowsf" "enable unfolding of class and map conditions in general" False,
    Param.flag "translation" "print first-order translation of sentences" False,
    Param.flag "tex" "parse passed file with forthel tex parser" False]

programFlags :: [Param.T Bool]
helpParam, serverParam, onlytranslateParam :: Param.T Bool
programFlags @ [helpParam, serverParam, onlytranslateParam] =
  [Param.flag "help" "show command-line help" False,
   Param.flag "server" "run in server mode" False,
   Param.flag "onlytranslate" "translate input text and exit" False]


-- Keywords

keywordsCommand :: [(Command, Text)]
keywordsCommand =
 [(EXIT, "exit"),
  (QUIT, "quit"),
  (THESIS, "thesis"),
  (CONTEXT, "context"),
  (FILTER, "filter"),
  (RULES, "rules")]

keywordsSynonym :: [([Text] -> Instr, Text)]
keywordsSynonym =
  [(Synonym, "synonym")]

paramName :: Param.T a -> Text
paramName p = Lazy.pack $ make_string $ Param.name p

keywordsLimit :: [(Int -> Instr, Text)]
keywordsLimit = map (\p -> (SetInt p, paramName p)) textLimits

keywordsFlag :: [(Bool -> Instr, Text)]
keywordsFlag = map (\p -> (SetBool p, paramName p)) textFlags

keywordsDropLimit, keywordsDropFlag :: [(Drop, Text)]
keywordsDropLimit = map (\p -> (DropInt p, paramName p)) textLimits
keywordsDropFlag = map (\p -> (DropBool p, paramName p)) textFlags

keywordsArgument :: [(Argument, Text)]
keywordsArgument =
 [(Read NonTex, "read"),
  (Read Tex, "readtex"),
  (Library, "library"),
  (Prover, "prover")]

-- distinguish between parser and verifier instructions

isParserInstruction :: Instr -> Bool
isParserInstruction i = case i of
  Command EXIT -> True
  Command QUIT -> True
  Synonym _ -> True
  GetArgument (Read _) _ -> True
  _ -> False
