-- |
-- Module      : SAD.Export.TPTP
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Print proof task in TPTP syntax.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.TPTP (
  Role(..),
  renderRole,
  Sequent,
  renderLogicFormula,
  renderSequent
) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.Data.Formula (Formula(..), showTrName, TermName(..))
import SAD.Helpers (failWithMessage)

import Isabelle.Position qualified as Position
import Isabelle.Library

import Naproche.TPTP (atomic_word)

data Role =
    Axiom
  | Hypothesis
  | Definition
  | Assumption
  | Lemma
  | Theorem
  | Corollary
  | Conjecture
  | NegatedConjecture
  | Plain
  | Type
  | Interpretation
  | FiDomain
  | FiFunctors
  | FiPredicates
  | Unknown

-- | Render a role.
renderRole :: Role -> Text
renderRole Axiom = "axiom"
renderRole Hypothesis = "hypothesis"
renderRole Definition = "definition"
renderRole Assumption = "assumption"
renderRole Lemma = "lemma"
renderRole Theorem = "theorem"
renderRole Corollary = "corollary"
renderRole Conjecture = "conjecture"
renderRole NegatedConjecture = "negated_conjecture"
renderRole Plain = "plain"
renderRole Type = "type"
renderRole Interpretation = "interpretation"
renderRole FiDomain = "fi_domain"
renderRole FiFunctors = "fi_functors"
renderRole FiPredicates = "fi_predicates"
renderRole Unknown = "unknown"

type Sequent = ([Formula], [Formula])

-- | Render a formula.
renderLogicFormula :: Text -> Role -> Formula -> Text
renderLogicFormula name role formula =
  "fof(m"
  <> (if Text.null name then "_" else name)
  <> ", " <> renderRole role <> ", "
  <> tptpTerm 0 formula
  <> ")."

-- | Render a sequent.
renderSequent :: Text -> Role -> Sequent -> Text
renderSequent name role (premises, conclusions) =
  "fof(m"
  <> (if Text.null name then "_" else name)
  <> ", " <> renderRole role <> ", ["
  <> Text.intercalate ", " (map (tptpTerm 0) premises)
  <> "] --> ["
  <> Text.intercalate ", " (map (tptpTerm 0) conclusions)
  <> "])."

tptpName :: Formula -> Text
tptpName = Text.fromStrict . make_text . atomic_word . make_bytes . showTrName

tptpTerm :: Int -> Formula -> Text
tptpTerm d = term
  where
    term (All _ f)  =  "( ! " <> binder f <> ")"
    term (Exi _ f)  = "( ? " <> binder f <> ")"
    term (Iff f g)  = sinfix " <=> " f g
    term (Imp f g)  = sinfix " => " f g
    term (Or  f g)  = sinfix " | " f g
    term (And f g)  = sinfix " & " f g
    term (Tag _ f)  = term f
    term (Not f)    = "( ~ " <> term f <> ")"
    term Top        = "$true"
    term Bot        = "$false"
    term t@Trm {trmName = TermEquality} = let [l, r] = trmArgs t in sinfix " = " l r
    term t@Trm {}   = tptpName t <> "(" <> Text.intercalate "," (map term $ trmArgs t) <> ")"
    term v@Var {}   = tptpName v
    term i@Ind {}   = "W" <> Text.pack (show (d - 1 - indIndex i))
    term ThisT      = failWithMessage "SAD.Export.TPTP" "Didn't expect ThisT here"

    sinfix o f g  = "(" <> term f <> o <> term g <> ")"

    binder f  = "[" <> tptpTerm (d + 1) (Ind 0 Position.none) <> "] : " <> tptpTerm (d + 1) f
