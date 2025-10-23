-- |
-- Module      : SAD.Data.Instr
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2018, 2022, Makarius Wenzel
-- License     : GPL-3
--
-- Instruction datatype and core functions.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Instr (
  ParserKind(..), Instr(..), Drop(..), Command(..),
  getInstr, addInstr, dropInstr,
  timelimitParam, memorylimitParam, depthlimitParam, checktimeParam, checkdepthParam,
  proveParam, checkParam, checkconsistencyParam, symsignParam, infoParam, thesisParam,
  filterParam, skipfailParam, flatParam, printgoalParam, printsectionParam, printcheckParam,
  printunfoldParam, printreasonParam, printproverParam, printfulltaskParam, dumpParam,
  printsimpParam, printthesisParam, unfoldParam, unfoldsfParam, unfoldlowParam, unfoldlowsfParam,
  translationParam,
  helpParam, serverParam, onlytranslateParam, onlytokenizeParam,
  modeParam, dialectParam, proverParam, texExeParam, bibtexExeParam, initParam, theoryParam,
  keywordsCommand, keywordsSynonym, keywordsLimit, keywordsFlag, keywordsArgument, keywordsModule,
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
data ParserKind = Ftl | Tex | Stex deriving (Eq, Ord)

instance Show ParserKind where
  show :: ParserKind -> String
  show Ftl = "FTL"
  show Tex = "TeX"
  show Stex = "sTeX"

data Instr =
    Command Command
  | Synonym [Text]
  | SetBool (Param.T Bool) Bool
  | SetInt (Param.T Int) Int
  | SetBytes (Param.T Bytes) Bytes
  | GetRelativeFilePath FilePath
  | GetAbsoluteFilePath FilePath
  | GetModule FilePath FilePath String
  | GetText Bytes
  | Verbose Bool
  deriving (Eq, Ord, Show)

data Drop =
    DropBool (Param.T Bool)
  | DropInt (Param.T Int)
  | DropBytes (Param.T Bytes)
  deriving (Eq, Ord, Show)


-- Instructions

data Command =
    ResetPretyping
  | PrintRules
  | PrintThesis
  | PrintContext
  | PrintContextFiltered
  | Exit
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
addInstr (GetRelativeFilePath _) = id
addInstr (GetModule _ _ _) = id
addInstr i = (:) i

dropInstr :: Drop -> [Instr] -> [Instr]
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

textArgs :: [Param.T Bytes]
modeParam, dialectParam, proverParam, texExeParam, bibtexExeParam :: Param.T Bytes
textArgs@[modeParam, dialectParam, proverParam, texExeParam, bibtexExeParam] =
   [Param.bytes "mode" "run Naproche in mode MODE" "verify",
    Param.bytes "dialect" "use the DIALECT dialect of ForTheL" "ftl",
    Param.bytes "prover" "use prover NAME" (Prover.get_name Prover.eprover),
    Param.bytes "tex-exe" "TeX executable EXE" "pdflatex",
    Param.bytes "bibtex-exe" "BibTeX executable EXE" "bibtex"]

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

helpParam, serverParam, onlytranslateParam, onlytokenizeParam :: Param.T Bool
helpParam = Param.flag "help" "show command-line help" False
serverParam = Param.flag "server" "run in server mode" False
onlytranslateParam = Param.flag "onlytranslate" "translate input text and exit" False
onlytokenizeParam = Param.flag "onlytokenize" "translate input text and exit" False


-- Keywords

keywordsCommand :: [(Command, Text)]
keywordsCommand =
 [(ResetPretyping, "resetpretyping"),
  (PrintRules, "rules"),
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
 [(GetRelativeFilePath . Lazy.unpack, "read")] ++
  map (paramKeyword (\p -> SetBytes p . make_bytes)) textArgs

keywordsModule :: [((FilePath, FilePath, String) -> Instr, Text)]
keywordsModule =
  [(\(x,y,z) -> GetModule x y z, "importmodule"),
   (\(x,y,z) -> GetModule x y z, "usemodule")]
