{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.Instr
-- Description : Instruction datatype and core functions.
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2018, 2022, Makarius Wenzel
-- License     : GPL-3
module SAD.Data.Instr (
  Dialect(..), Mode(..), Instr(..), Drop(..), Command(..),
  getInstr, addInstr, dropInstr,
  timelimitParam, memorylimitParam, depthlimitParam, checktimeParam, checkdepthParam,
  proveParam, checkParam, checkconsistencyParam, symsignParam, infoParam, thesisParam,
  filterParam, skipfailParam, flatParam, printgoalParam, printsectionParam, printcheckParam,
  printunfoldParam, printreasonParam, printproverParam, printfulltaskParam, dumpParam,
  printsimpParam, printthesisParam, unfoldParam, unfoldsfParam, unfoldlowParam, unfoldlowsfParam,
  translationParam,
  helpParam, serverParam, quietParam, verboseParam,
  modeParam, dialectParam, proverParam,
  keywordsCommand, keywordsSynonym, keywordsLimit, keywordsFlag, keywordsProver,
  keywordsPath, keywordsDropLimit, keywordsDropFlag
) where

import Data.Text (Text)

import Isabelle.Bytes (Bytes)

import Naproche.Param qualified as Param
import Naproche.Prover (Prover)
import Naproche.Prover qualified as Prover

import SAD.Export.Pretty


-- Instructions

data Instr =
    Command Command
  | Synonym [Text]
  | SetBool (Param.T Bool) Bool
  | SetInt (Param.T Int) Int
  | SetMode (Param.T Mode) Mode
  | SetDialect (Param.T Dialect) Dialect
  | SetProver (Param.T Prover) Prover
  | GetRelativeFilePath FilePath
  | GetAbsoluteFilePath FilePath
  | GetModule FilePath FilePath String
  | GetText Bytes
  deriving (Show)

data Drop =
    DropBool (Param.T Bool)
  | DropInt (Param.T Int)
  | DropBytes (Param.T Bytes)
  deriving (Show)


-- Commands

data Command =
    ResetPretyping
  | PrintRules
  | PrintThesis
  | PrintContext
  | PrintContextFiltered
  | Exit
  deriving (Show)


-- Modes

data Mode
  = Lex_Mode
  | Tokenize_Mode
  | Translate_Mode
  | Verify_Mode
  deriving (Eq, Show)

mode_args :: [(Bytes, Mode)]
mode_args = [
    ("lex", Lex_Mode),
    ("tokenize", Tokenize_Mode),
    ("translate", Translate_Mode),
    ("verify", Verify_Mode)
  ]


-- Dialects

data Dialect
  = Ftl_Dialect
  | Tex_Dialect
  | Stex_Dialect
  deriving (Eq, Show)

instance Pretty Dialect where
  pretty_print Ftl_Dialect = "FTL"
  pretty_print Tex_Dialect = "TeX"
  pretty_print Stex_Dialect = "sTeX"

dialect_args :: [(Bytes, Dialect)]
dialect_args = [
    ("ftl", Ftl_Dialect),
    ("tex", Tex_Dialect),
    ("stex", Stex_Dialect)
  ]


-- instruction environment

getInstr :: Param.T a -> [Instr] -> a
getInstr p = Param.get p . foldr instr Param.empty
  where
    instr :: Instr -> Param.Env -> Param.Env
    instr (SetBool p x)
      | p == quietParam && x = \env -> foldr (`Param.put` False) env verboseFlags
      | p == verboseParam && x = \env -> foldr (`Param.put` True) env verboseFlags
      | otherwise = Param.put p x
    instr (SetInt p x) = Param.put p x
    instr (SetMode p x) = Param.put p x
    instr (SetDialect p x) = Param.put p x
    instr (SetProver p x) = Param.put p x
    instr _ = id

addInstr :: Instr -> [Instr] -> [Instr]
addInstr (Synonym _) = id
addInstr (GetRelativeFilePath _) = id
addInstr (GetModule {}) = id
addInstr i = (:) i

dropInstr :: Drop -> [Instr] -> [Instr]
dropInstr (DropBool p) (SetBool p' _ : rs) | p == p' = rs
dropInstr (DropInt p) (SetInt p' _ : rs) | p == p' = rs
dropInstr i (r : rs) = r : dropInstr i rs
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
  translationParam :: Param.T Bool
textFlags@[proveParam, checkParam, checkconsistencyParam, symsignParam, infoParam, thesisParam,
  filterParam, skipfailParam, flatParam, printgoalParam, printsectionParam, printcheckParam,
  printunfoldParam, printreasonParam, printproverParam, printfulltaskParam, dumpParam,
  printsimpParam, printthesisParam, unfoldParam, unfoldsfParam, unfoldlowParam, unfoldlowsfParam,
  translationParam] =
   [Param.flag "prove" "prove goals in the text" True,
    Param.flag "check" "check symbols for definedness" True,
    Param.flag "checkconsistency" "check that no contradictory axioms occur" False,
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
    Param.flag "translation" "print first-order translation of sentences" False]

modeParam :: Param.T Mode
modeParam = Param.generic (get_arg_key mode_args) (get_arg_value mode_args) "mode" "run Naproche in mode MODE" Verify_Mode

dialectParam :: Param.T Dialect
dialectParam = Param.generic (get_arg_key dialect_args) (get_arg_value dialect_args) "dialect" "use ForTheL dialect DIALECT" Ftl_Dialect

proverParam :: Param.T Prover
proverParam = Param.generic Prover.get_name Prover.find "prover" "use prover NAME" Prover.eprover

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

helpParam, serverParam, quietParam, verboseParam :: Param.T Bool
helpParam = Param.flag "help" "show command-line help" False
serverParam = Param.flag "server" "run in server mode" False
quietParam = Param.flag "quiet" "print no details" False
verboseParam = Param.flag "verbose" "print more details" False


-- Keywords

keywordsCommand :: [(Command, Bytes)]
keywordsCommand = [
    (ResetPretyping, "resetpretyping"),
    (PrintRules, "rules"),
    (PrintThesis, "thesis"),
    (PrintContext, "context"),
    (PrintContextFiltered, "filter"),
    (Exit, "exit")
  ]

keywordsSynonym :: [([Text] -> Instr, Bytes)]
keywordsSynonym = [(Synonym, "synonym")]

keywordsPath :: [(FilePath -> Instr, Bytes)]
keywordsPath = [(GetRelativeFilePath, "read")]

keywordsLimit :: [(Int -> Instr, Bytes)]
keywordsLimit = map (paramKeyword SetInt) textLimits

keywordsFlag :: [(Bool -> Instr, Bytes)]
keywordsFlag = map (paramKeyword SetBool) textFlags

keywordsProver :: [(Prover -> Instr, Bytes)]
keywordsProver = [paramKeyword SetProver proverParam]

keywordsDropLimit, keywordsDropFlag :: [(Drop, Bytes)]
keywordsDropLimit = map (paramKeyword DropInt) textLimits
keywordsDropFlag = map (paramKeyword DropBool) textFlags


-- Helpers

get_arg_value :: [(Bytes, a)] -> Bytes -> Maybe a
get_arg_value [] _ = Nothing
get_arg_value ((key, value) : rest) k = if key == k
  then Just value
  else get_arg_value rest k

get_arg_key :: Eq a => [(Bytes, a)] -> a -> Bytes
get_arg_key [] _ = error "Invalid value"
get_arg_key ((key, value) : rest) v = if value == v
  then key
  else get_arg_key rest v

paramKeyword :: (Param.T a -> b) -> Param.T a -> (b, Bytes)
paramKeyword f p = (f p, Param.name p)

