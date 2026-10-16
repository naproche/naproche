-- |
-- Module      : SAD.Export.TPTP
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Print proof task in TPTP syntax.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.TPTP (
  exportProofTask
) where

import Data.Text (Text)
import Data.Text qualified as Text

import SAD.Data.Text.Context (Context(..))
import SAD.Data.Text.Block qualified as Block
import SAD.Data.Formula (Formula(..), showTrName, TermName(..))

import Isabelle.Position qualified as Position
import Isabelle.Library

import Naproche.TPTP (atomic_word)

-- | The role of an assertion, i.e. whether it is a hypothesis or a conjecture.
data Role =
    Hypothesis
  | Conjecture

-- | Export a role to TPTP.
exportRole :: Role -> Text
exportRole Hypothesis = "hypothesis"
exportRole Conjecture = "conjecture"

-- | Export a proof task to TPTP.
exportProofTask :: [Context] -> Context -> Text
exportProofTask contexts goal =
  Text.unlines (map (exportContext Hypothesis) $ reverse contexts)
  <> "\n" <> exportContext Conjecture goal

-- | Export a context to TPTP.
exportContext :: Role -> Context -> Text
exportContext role (Context formula (Block.Block { Block.name = name } : _) _) =
  exportAssertion name role formula
exportContext _ _ = ""

-- | Export an assertion to TPTP.
exportAssertion :: Text -> Role -> Formula -> Text
exportAssertion name role formula =
  "fof(m"
  <> (if Text.null name then "_" else name)
  <> ", " <> exportRole role <> ", "
  <> exportFormula formula
  <> ")."

-- | Export a term name to TPTP.
exportTermName :: Formula -> Text
exportTermName = make_text . atomic_word . make_bytes . showTrName

-- | Export a formula to TPTP.
exportFormula :: Formula -> Text
exportFormula = exportFormula' 0
  where
    exportFormula' d (All _ f) =  "( ! " <> binder d f <> ")"
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
    exportFormula' d t@Trm {}
      | null (trmArgs t) = exportTermName t
      | otherwise = exportTermName t <> "(" <> Text.intercalate "," (map (exportFormula' d) $ trmArgs t) <> ")"
    exportFormula' d v@Var {}= exportTermName v
    exportFormula' d i@Ind {}= "W" <> show_text (d - 1 - indIndex i)
    exportFormula' d ThisT = "Didn't expect ThisT here"

    sinfix d o f g  = "(" <> exportFormula' d f <> o <> exportFormula' d g <> ")"

    binder d f  = "[" <> exportFormula' (d + 1) (Ind 0 Position.none) <> "] : " <> exportFormula' (d + 1) f
