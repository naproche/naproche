-- |
-- Module      : SAD.Structures.Formula
-- Copyright   : (c) 2020, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


module SAD.Structures.Formula where

import Data.Text.Lazy (Text)


newtype Document = Document [Declaration] deriving Show

data Declaration
  = Hypothesis Text [Assumption]
  | Conjecture Text [Assumption] Statement
  | Inductive Assumption [[Assumption]]
  deriving (Show, Eq)

type Assumption = Formula
type Statement = Formula

data Formula
  = Variable Text
  | All Text Formula
  | Exists Text Formula
  | Predicate Text
  | TyPredicate Text
  | Const Text
  | Formula :@ Formula
  | Formula :/\ Formula
  | Formula :\/ Formula
  | Formula :-> Formula
  | Formula :<-> Formula
  | Formula :== Formula
  | Bot | Top
  deriving (Show, Eq)

infixl 6 :@
infixl 5 :/\
infixl 4 :<->
infixl 4 :->
