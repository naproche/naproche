{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Export.TPTP
-- Description : Print proof task in TPTP (fof) syntax.
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2026, Marcel Schütz
-- License     : GPL-3
module SAD.Export.TPTP (
  exportProofTask
) where

import Data.Text (Text)
import Data.Text qualified as Text

import Isabelle.Bytes (Bytes)
import Isabelle.Library (cat_lines, commas, make_bytes, make_string, quote,
                         show_bytes, show_text)
import Isabelle.Position qualified as Position

import Naproche.TPTP (atomic_word)

import SAD.Data.Formula (Formula(..), TermName(..))
import SAD.Data.Text.Block qualified as Block
import SAD.Data.Text.Context (Context(..))
import SAD.Data.VarName (VariableName(..))

-- | The role of an assertion, i.e. whether it is a hypothesis or a conjecture.
data Role =
    Hypothesis
  | Conjecture

-- | Export a role to TPTP.
exportRole :: Role -> Bytes
exportRole Hypothesis = "hypothesis"
exportRole Conjecture = "conjecture"

-- | Export a proof task to TPTP.
exportProofTask :: [Context] -> Context -> Bytes
exportProofTask contexts goal =
  cat_lines (map (exportContext Hypothesis) $ reverse contexts)
  <> "\n" <> exportContext Conjecture goal

-- | Export a context to TPTP.
exportContext :: Role -> Context -> Bytes
exportContext role (Context formula (Block.Block { Block.name = name } : _) _) =
  exportAssertion name role formula
exportContext _ _ = ""

-- | Export an assertion to TPTP.
exportAssertion :: Text -> Role -> Formula -> Bytes
exportAssertion name role formula =
  "fof(m"
  <> (if Text.null name then "_" else make_bytes name)
  <> ", " <> exportRole role <> ", "
  <> exportFormula formula
  <> ")."

-- | Export a term name to TPTP.
exportTermName :: TermName -> Bytes
exportTermName = atomic_word . make_bytes . exportTermName'
  where
    exportTermName' (TermName t) = t
    exportTermName' (TermSymbolic t) = "s" <> t
    exportTermName' (TermNotion t) = "a" <> t
    exportTermName' (TermThe t) = "the" <> t
    exportTermName' (TermUnaryAdjective t) = "is" <> t
    exportTermName' (TermMultiAdjective t) = "mis" <> t
    exportTermName' (TermUnaryVerb t) = "do" <> t
    exportTermName' (TermMultiVerb t) = "mdo" <> t
    exportTermName' (TermTask n) = "tsk " <> show_text n
    exportTermName' TermEquality = "="
    exportTermName' TermLess = "iLess"
    exportTermName' TermThesis = "#TH#"

-- | Export a variable name to TPTP.
exportVariableName :: VariableName -> Bytes
exportVariableName = atomic_word . make_bytes . exportVariableName'
  where
    exportVariableName' (VarConstant s) = "x" <> s
    exportVariableName' (VarHole s) = "?" <> s
    exportVariableName' VarSlot = "!"
    exportVariableName' (VarU s) = "u" <> s
    exportVariableName' (VarHidden n) = "h" <> show_text n
    exportVariableName' (VarAssume n) = "i" <> show_text n
    exportVariableName' (VarSkolem n) = "o" <> show_text n
    exportVariableName' (VarTask s) = "c" <> exportVariableName' s
    exportVariableName' (VarZ s) = "z" <> s
    exportVariableName' (VarW s) = "w" <> s
    exportVariableName' VarEmpty = ""
    exportVariableName' (VarDefault s) = s

-- | Export a formula to TPTP.
exportFormula :: Formula -> Bytes
exportFormula = exportFormula' 0
  where
    exportFormula' d (All _ f) = "( ! " <> binder d f <> ")"
    exportFormula' d (Exi _ f) = "( ? " <> binder d f <> ")"
    exportFormula' d (Iff f g) = sinfix d " <=> " f g
    exportFormula' d (Imp f g) = sinfix d " => " f g
    exportFormula' d (Or  f g) = sinfix d " | " f g
    exportFormula' d (And f g) = sinfix d " & " f g
    exportFormula' d (Tag _ f) = exportFormula' d f
    exportFormula' d (Not f) = "( ~ " <> exportFormula' d f <> ")"
    exportFormula' d Top = "$true"
    exportFormula' d Bot = "$false"
    exportFormula' d t@Trm {trmName = TermEquality} = let [l, r] = trmArgs t in sinfix d " = " l r
    exportFormula' d t@Trm {trmName = s}
      | null (trmArgs t) = exportTermName s
      | otherwise = exportTermName s <> "(" <> commas (map (exportFormula' d) $ trmArgs t) <> ")"
    exportFormula' d v@Var {varName = s} = exportVariableName s
    exportFormula' d i@Ind {} = "W" <> show_bytes (d - 1 - indIndex i)
    exportFormula' d ThisT = error $ "unexpected " <> quote "ThisT"

    sinfix d o f g = "(" <> exportFormula' d f <> o <> exportFormula' d g <> ")"

    binder d f = "[" <> exportFormula' (d + 1) (Ind 0 Position.none) <> "] : " <> exportFormula' (d + 1) f
