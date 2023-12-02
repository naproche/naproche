-- |
-- Authors: Andrei Paskevich (2001 - 2008),
--          Steffen Frerix (2017 - 2018),
--          Makarius Wenzel (2018, 2022)
--
-- Instruction datatype and core functions.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Instr (
  ParserKind(..), Instr(..), Drop(..), Command(..), Argument(..),
  getInstr, addInstr, dropInstr,
  timelimitParam, memorylimitParam, depthlimitParam, checktimeParam, checkdepthParam,
  proveParam, checkParam, checkconsistencyParam, symsignParam, infoParam, thesisParam,
  filterParam, skipfailParam, flatParam, printgoalParam, printsectionParam, printcheckParam,
  printunfoldParam, printreasonParam, printproverParam, printfulltaskParam, dumpParam,
  printsimpParam, printthesisParam, unfoldParam, unfoldsfParam, unfoldlowParam, unfoldlowsfParam,
  translationParam, texParam,
  helpParam, serverParam, onlytranslateParam,
  libraryParam, proverParam, initParam, theoryParam,
  keywordsCommand, keywordsSynonym, keywordsLimit, keywordsFlag, keywordsArgument,
  keywordsDropLimit, keywordsDropFlag
) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Lazy

import Isabelle.Bytes (Bytes)
import Isabelle.Library

import Naproche.Param qualified as Param
import Naproche.Prover qualified as Prover


-- Instruction types

-- | Indicate which of the parsers is currently used. This is must be recorded in the State
-- for read instruction to work properly.
data ParserKind = Ftl | Tex deriving (Eq, Ord, Show)

data Instr =
    Command Command
  | Synonym [Text]
  | SetBool (Param.T Bool) Bool
  | SetInt (Param.T Int) Int
  | SetBytes (Param.T Bytes) Bytes
  | GetArgument Argument Text
  | Verbose Bool
  deriving (Eq, Ord, Show)

data Drop =
    DropCommand Command
  | DropBool (Param.T Bool)
  | DropInt (Param.T Int)
  | DropBytes (Param.T Bytes)
  deriving (Eq, Ord, Show)


-- Instructions

data Command =
    PrintRules
  | PrintThesis
  | PrintContext
  | PrintContextFiltered
  | Exit
  deriving (Eq, Ord, Show)

data Argument =
    Text ParserKind    --  literal text
  | File ParserKind    --  read file
  | Read ParserKind    --  read library file
  deriving (Eq, Ord, Show)


-- instruction environment

getInstr :: Param.T a -> [Instr] -> a
getInstr p = Param.get p . foldr instr Param.empty
  where
    instr :: Instr -> Param.Env -> Param.Env
    instr (SetBool p x) = Param.put p x
    instr (SetInt p x) = Param.put p x
    instr (SetBytes p x) = Param.put p (make_bytes x)
    instr (Verbose b) = \env -> foldr (`Param.put` b) env verboseFlags
    instr _ = id

addInstr :: Instr -> [Instr] -> [Instr]
addInstr (Synonym _) = id
addInstr (GetArgument (Read _) _) = id
addInstr i = (:) i

dropInstr :: Drop -> [Instr] -> [Instr]
dropInstr (DropCommand m) (Command n : rs) | n == m = rs
dropInstr (DropBool p) (SetBool p' _ : rs) | p == p' = rs
dropInstr (DropInt p) (SetInt p' _ : rs) | p == p' = rs
dropInstr (DropBytes p) (SetBytes p' _ : rs) | p == p' = rs
dropInstr i (r : rs)  = r : dropInstr i rs
dropInstr _ _ = []


-- Parameters

textLimits :: [Param.T Int]
timelimitParam, memorylimitParam, depthlimitParam, checktimeParam, checkdepthParam :: Param.T Int
textLimits@[timelimitParam, memorylimitParam, depthlimitParam, checktimeParam, checkdepthParam] =
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
textFlags@[proveParam, checkParam, checkconsistencyParam, symsignParam, infoParam, thesisParam,
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

textArgs :: [Param.T Bytes]
libraryParam, proverParam :: Param.T Bytes
textArgs@[libraryParam, proverParam] =
  [Param.bytes "library" "place to look for library texts" "NAPROCHE_LIBRARY",
   Param.bytes "prover" "use prover NAME" (Prover.get_name Prover.eprover)]

initParam, theoryParam :: Param.T Bytes
initParam = Param.bytes "init" "init file, empty to skip" "init.opt"
theoryParam = Param.bytes "theory" "choose the underlying theory" "fol"

verboseFlags :: [Param.T Bool]
verboseFlags =
  [printgoalParam,
   printsectionParam,
   printcheckParam,
   printunfoldParam,
   printreasonParam,
   printproverParam,
   printfulltaskParam,
   printsimpParam,
   printthesisParam]

helpParam, serverParam, onlytranslateParam :: Param.T Bool
helpParam = Param.flag "help" "show command-line help" False
serverParam = Param.flag "server" "run in server mode" False
onlytranslateParam = Param.flag "onlytranslate" "translate input text and exit" False


-- Keywords

keywordsCommand :: [(Command, Text)]
keywordsCommand =
 [(PrintRules, "rules"),
  (PrintThesis, "thesis"),
  (PrintContext, "context"),
  (PrintContextFiltered, "filter"),
  (Exit, "exit"),
  (Exit, "quit")]

keywordsSynonym :: [([Text] -> Instr, Text)]
keywordsSynonym =
  [(Synonym, "synonym")]


paramKeyword :: (Param.T a -> b) -> Param.T a -> (b, Text)
paramKeyword f p = (f p, Lazy.pack $ make_string $ Param.name p)

keywordsLimit :: [(Int -> Instr, Text)]
keywordsLimit = map (paramKeyword SetInt) textLimits

keywordsFlag :: [(Bool -> Instr, Text)]
keywordsFlag = map (paramKeyword SetBool) textFlags

keywordsDropLimit, keywordsDropFlag :: [(Drop, Text)]
keywordsDropLimit = map (paramKeyword DropInt) textLimits
keywordsDropFlag = map (paramKeyword DropBool) textFlags

keywordsArgument :: [(Text -> Instr, Text)]
keywordsArgument =
 [(GetArgument $ Read Ftl, "read"),
  (GetArgument $ Read Tex, "readtex")] ++
  map (paramKeyword (\p -> SetBytes p . make_bytes)) textArgs
