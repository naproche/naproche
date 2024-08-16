-- |
-- Module      : SAD.Data.Formula.Show
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Show instance for formulas.


{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Formula.Show () where

import Data.Text.Lazy qualified as Text
import Data.List qualified as List

import SAD.Data.Formula.Base
import SAD.Data.Formula.Kit
import SAD.Data.VarName
import SAD.Data.Terms
import SAD.Export.Representation (toLazyText, represent)

import Isabelle.Position qualified as Position
import SAD.Helpers


instance Show Formula where
  show :: Formula -> String
  show = showFormula 0

-- | Show a formula (depending of the current nesting depth of quantifiers).
showFormula :: Int -> Formula -> String
-- Quantifier chain:
showFormula d (All _ f@(All _ _)) = "\\<forall>" ++ showBindingVar d ++ showFormula (d + 1) f
showFormula d (All _ f@(Exi _ _)) = "\\<forall>" ++ showBindingVar d ++ showFormula (d + 1) f
showFormula d (All _ f@(Not (Exi _ _))) = "\\<forall>" ++ showBindingVar d ++ showFormula (d + 1) f
showFormula d (Exi _ f@(All _ _)) = "\\<exists>" ++ showBindingVar d ++ showFormula (d + 1) f
showFormula d (Exi _ f@(Exi _ _)) = "\\<exists>" ++ showBindingVar d ++ showFormula (d + 1) f
showFormula d (Exi _ f@(Not (Exi _ _))) = "\\<exists>" ++ showBindingVar d ++ showFormula (d + 1) f
showFormula d (Not (Exi _ f@(All _ _))) = "\\<nexists>" ++ showBindingVar d ++ showFormula (d + 1) f
showFormula d (Not (Exi _ f@(Exi _ _))) = "\\<nexists>" ++ showBindingVar d ++ showFormula (d + 1) f
showFormula d (Not (Exi _ f@(Not (Exi _ _)))) = "\\<nexists>" ++ showBindingVar d ++ showFormula (d + 1) f
-- Single quantifier:
showFormula d (All _ f) = "\\<forall>" ++ showBindingVar d ++ parens (showFormula (d + 1) f)
showFormula d (Exi _ f) = "\\<exists>" ++ showBindingVar d ++ parens (showFormula (d + 1) f)
-- Negated existential quantifier:
showFormula d (Not (Exi _ f)) = "\\<nexists>" ++ showBindingVar d ++ parens (showFormula (d + 1) f)
-- Equivalence:
showFormula d (Iff f g) = showFormulaL d f ++ " \\<Longleftrightarrow> " ++ showFormulaR d g
-- Implication:
showFormula d (Imp f g) = showFormulaL d f ++ " \\<Longrightarrow> " ++ showFormulaR d g
-- Disjunction chain:
showFormula d (Or f@(Or _ _) g) = showFormula d f ++ " \\<or> " ++ showFormulaR d g
showFormula d (Or f g@(Or _ _)) = showFormulaL d f ++ " \\<or> " ++ showFormula d g
-- Disjunction:
showFormula d (Or  f g) = showFormulaL d f ++ " \\<or> " ++ showFormulaR d g
-- Conjunction chain:
showFormula d (And f@(And _ _) g) = showFormula d f ++ " \\<and> " ++ showFormulaR d g
showFormula d (And f g@(And _ _)) = showFormulaL d f ++ " \\<and> " ++ showFormula d g
-- Conjunction:
showFormula d (And f g) = showFormulaL d f ++ " \\<and> " ++ showFormulaR d g
-- Tagged formula:
showFormula d (Tag a f) = show a ++ " \\<Colon> " ++ showFormulaR d f
-- Inequality:
showFormula d (Not Trm{trmName = TermEquality, trmArgs = [l, r]}) = showFormula d l ++ " \\<noteq> " ++ showFormula d r
-- Negation:
showFormula d (Not f) = "\\<not>" ++ showFormulaR d f
-- Truth:
showFormula d Top = "\\<top>"
-- Falsity:
showFormula d Bot = "\\<bottom>"
-- @ThisT@:
showFormula d ThisT = "ThisT"
-- Thesis:
showFormula d Trm{trmName = TermThesis} = "thesis"
-- Equality:
showFormula d Trm{trmName = TermEquality, trmArgs = [l, r]} = showFormula d l ++ " = " ++ showFormula d r
-- Symbolic formula/term:
showFormula d Trm{trmName = TermSymbolic tName, trmArgs = tArgs} = substitute (Text.unpack tName) tArgs d
-- Non-symbolic formula/term:
showFormula d Trm{trmName = tName, trmArgs = tArgs} = Text.unpack (toLazyText (represent tName)) ++ showArguments d tArgs
-- Free variables:
showFormula d Var{varName = VarConstant s} = Text.unpack s
showFormula d Var{varName = vName} = Text.unpack $ toLazyText $ represent vName
-- De Brujin index:
showFormula d Ind{indIndex = i}
  | i < d = "v" ++ show (d - i - 1)
  | otherwise = "v?" ++ show i

-- | Show a formula that occurs on the left-hand side of a logical connective.
showFormulaL :: Int -> Formula -> String
showFormulaL d f = parensIf (isAll f || isExi f || isIff f || isImp f || isOr f || isAnd f || isTag f) (showFormula d f)

-- | Show a formula that occurs on the right-hand side of a logical connective.
showFormulaR :: Int -> Formula -> String
showFormulaR d f = parensIf (isIff f || isImp f || isOr f || isAnd f || isTag f) (showFormula d f)

-- | Show the arguments of a formula/term.
showArguments :: Int -> [Formula] -> String
showArguments _ [] = ""
showArguments d terms =
  let showTerm = showFormula d
  in "(" ++ List.intercalate "," (map showTerm terms) ++ ")"

-- | Show a binding variable.
showBindingVar :: Int -> String
showBindingVar d = showFormula (d + 1) (Ind 0 Position.none)

-- | Substitute all @.@ characters in a string by given terms.
substitute :: String -> [Formula] -> Int -> String
substitute s [] _ = s
substitute s (t : ts) d = dec s
  where
    dec ('.' : cs) = parensIf (ambig t) (showFormula d t) ++ substitute cs ts d
    dec (c : cs@('.' : _)) | isAsciiLetter c = c : " " ++ dec cs
    dec (c : cs) = c : dec cs
    dec [] = ""

    ambig Trm {trmName = TermSymbolic tName} =
      ("." `Text.isPrefixOf` tName && Text.drop 2 tName /= "(.)") ||
      "." `Text.isSuffixOf` tName
    ambig _ = False
