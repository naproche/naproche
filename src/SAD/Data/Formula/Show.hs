{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.Formula.Show
-- Description : Show instance for formulas.
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2024, Marcel Schütz
-- License     : GPL-3
module SAD.Data.Formula.Show () where

import Data.Text (Text)
import Data.Text qualified as Text

import Isabelle.Library (show_text)
import Isabelle.Position qualified as Position

import SAD.Data.Formula.Base
import SAD.Data.Formula.Kit
import SAD.Data.Pattern
import SAD.Data.Terms
import SAD.Data.VarName
import SAD.Export.Presentation


instance Presentation Formula where
  present = showFormula 0

instance Show Formula where
  show = Text.unpack . present

-- | Show a formula (depending of the current nesting depth of quantifiers).
showFormula :: Int -> Formula -> Text
-- Quantifier chain:
showFormula d (All _ f@(All _ _)) = "\\<forall>" <> showBindingVar d <> showFormula (d + 1) f
showFormula d (All _ f@(Exi _ _)) = "\\<forall>" <> showBindingVar d <> showFormula (d + 1) f
showFormula d (All _ f@(Not (Exi _ _))) = "\\<forall>" <> showBindingVar d <> showFormula (d + 1) f
showFormula d (Exi _ f@(All _ _)) = "\\<exists>" <> showBindingVar d <> showFormula (d + 1) f
showFormula d (Exi _ f@(Exi _ _)) = "\\<exists>" <> showBindingVar d <> showFormula (d + 1) f
showFormula d (Exi _ f@(Not (Exi _ _))) = "\\<exists>" <> showBindingVar d <> showFormula (d + 1) f
showFormula d (Not (Exi _ f@(All _ _))) = "\\<nexists>" <> showBindingVar d <> showFormula (d + 1) f
showFormula d (Not (Exi _ f@(Exi _ _))) = "\\<nexists>" <> showBindingVar d <> showFormula (d + 1) f
showFormula d (Not (Exi _ f@(Not (Exi _ _)))) = "\\<nexists>" <> showBindingVar d <> showFormula (d + 1) f
-- Single quantifier:
showFormula d (All _ f) = "\\<forall>" <> showBindingVar d <> parens (showFormula (d + 1) f)
showFormula d (Exi _ f) = "\\<exists>" <> showBindingVar d <> parens (showFormula (d + 1) f)
-- Negated existential quantifier:
showFormula d (Not (Exi _ f)) = "\\<nexists>" <> showBindingVar d <> parens (showFormula (d + 1) f)
-- Equivalence:
showFormula d (Iff f g) = showFormulaL d f <> " \\<Longleftrightarrow> " <> showFormulaR d g
-- Implication:
showFormula d (Imp f g) = showFormulaL d f <> " \\<Longrightarrow> " <> showFormulaR d g
-- Disjunction chain:
showFormula d (Or f@(Or _ _) g) = showFormula d f <> " \\<or> " <> showFormulaR d g
showFormula d (Or f g@(Or _ _)) = showFormulaL d f <> " \\<or> " <> showFormula d g
-- Disjunction:
showFormula d (Or  f g) = showFormulaL d f <> " \\<or> " <> showFormulaR d g
-- Conjunction chain:
showFormula d (And f@(And _ _) g) = showFormula d f <> " \\<and> " <> showFormulaR d g
showFormula d (And f g@(And _ _)) = showFormulaL d f <> " \\<and> " <> showFormula d g
-- Conjunction:
showFormula d (And f g) = showFormulaL d f <> " \\<and> " <> showFormulaR d g
-- Tagged formula:
showFormula d (Tag a f) = Text.pack (show a) <> " \\<Colon> " <> showFormulaR d f
-- Inequality:
showFormula d (Not Trm{trmName = TermEquality, trmArgs = [l, r]}) = showFormula d l <> " \\<noteq> " <> showFormula d r
-- Negation:
showFormula d (Not f) = "\\<not>" <> showFormulaR d f
-- Truth:
showFormula d Top = "\\<top>"
-- Falsity:
showFormula d Bot = "\\<bottom>"
-- @ThisT@:
showFormula d ThisT = "ThisT"
-- Terms:
showFormula d Trm{trmName = name, trmArgs = args} = showTerm d name args
-- Free variables:
showFormula d Var{varName = VarConstant s} = s
showFormula d Var{varName = vName} = present vName
-- De Brujin index:
showFormula d Ind{indIndex = i}
      | i < d = "v" <> Text.pack (show (d - i - 1))
      | otherwise = "v?" <> Text.pack (show i)

showTerm :: Int -> TermName -> [Formula] -> Text
showTerm d (TermSymbolic patterns) formulas = dive patterns formulas
  where
    dive :: SymbolPattern -> [Formula] -> Text
    dive [] _ = ""
    dive [SymbSymbol s] _ = s
    dive (SymbSymbol s : ps) fs = s <> " " <> dive ps fs
    dive (SymbVar : ps) [] = error "Fewer arguments than variables"
    dive [SymbVar] (f : _) = showFormula d f
    dive (SymbVar : ps) (f : fs) = showFormula d f <> " " <> dive ps fs
showTerm d (TermNotion pattern) formulas = "a" <> showNotionPattern pattern <> showArguments d formulas
showTerm d (TermThe pattern) formulas = "the" <> showNotionPattern pattern <> showArguments d formulas
showTerm d (TermUnaryAdjective pattern) formulas = "is" <> showPredicatePattern pattern <> showArguments d formulas
showTerm d (TermMultiAdjective pattern) formulas = "mis" <> showPredicatePattern pattern <> showArguments d formulas
showTerm d (TermUnaryVerb pattern) formulas = "do" <> showPredicatePattern pattern <> showArguments d formulas
showTerm d (TermMultiVerb pattern) formulas = "mdo" <> showPredicatePattern pattern <> showArguments d formulas
showTerm _ (TermTask n) _ = "tsk_" <> show_text n
showTerm d TermEquality [l, r] = showFormula d l <> " = " <> showFormula d r
showTerm _ TermEquality _ = error "Invalid number of arguments"
showTerm d TermLess formulas = "iLess" <> showArguments d formulas
showTerm _ TermThesis _ = "#TH#"

showPredicatePattern :: PredicatePattern -> Text
showPredicatePattern = foldr ((<>) . showPredicatePatternComp) ""

showPredicatePatternComp :: PredicatePatternComp -> Text
showPredicatePatternComp (PredWord words) = Text.toTitle (head words)
showPredicatePatternComp PredVar = ""

showNotionPattern :: NotionPattern -> Text
showNotionPattern = foldr ((<>) . showNotionPatternComp) ""

showNotionPatternComp :: NotionPatternComp -> Text
showNotionPatternComp (NotionWord words) = Text.toTitle (head words)
showNotionPatternComp NotionName = ""
showNotionPatternComp NotionVar = ""

-- | Show a formula that occurs on the left-hand side of a logical connective.
showFormulaL :: Int -> Formula -> Text
showFormulaL d f = parensIf (isAll f || isExi f || isIff f || isImp f || isOr f || isAnd f || isTag f) (showFormula d f)

-- | Show a formula that occurs on the right-hand side of a logical connective.
showFormulaR :: Int -> Formula -> Text
showFormulaR d f = parensIf (isIff f || isImp f || isOr f || isAnd f || isTag f) (showFormula d f)

-- | Show the arguments of a formula/term.
showArguments :: Int -> [Formula] -> Text
showArguments _ [] = ""
showArguments d terms =
  let showTerm = showFormula d
  in "(" <> Text.intercalate "," (map showTerm terms) <> ")"

-- | Show a binding variable.
showBindingVar :: Int -> Text
showBindingVar d = showFormula (d + 1) (Ind 0 Position.none)

-- | Wrap a string in parentheses.
parens :: Text -> Text
parens string = "(" <> string <> ")"

-- | Wrap a string in parentheses if a predicate holds true, otherwise return
-- the string unmodified.
parensIf :: Bool -> Text -> Text
parensIf pred string = if pred then parens string else string
