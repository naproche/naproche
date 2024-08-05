-- |
-- Module      : SAD.Structures.Type
-- Copyright   : (c) 2020, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


module SAD.Structures.Type where

import Data.Text.Lazy (Text)


data Expr

  = Const Text

  | Variable Text

  -- `Pi a A F` represents the type `∏(a : A) F(a)`.
  | Pi Text Expr Expr
  | All Text Expr Expr
  | Expr :-> Expr

  -- `Exists a A F` represents the type `∃(a : A) F(a)`.
  | Exists Text Expr Expr
  | Expr :/\ Expr

  -- Coproduct
  | Expr :\/ Expr
  | Expr :<-> Expr

  -- Function application
  | Expr :@ Expr

  -- `Abs a A T` represents `λ(a : A) T(a)`
  | Abs Text Expr Expr

  -- `Omit` inhabits every proposition.
  | Omit

  -- For leaving expressions to be inferred by the elaborator.
  | Hole

  | Top
  | Bot

  deriving (Eq, Show)


type Typ = Expr

infixr 4 -->
infixr 5 \/
infixr 5 /\
infixl 6 <@>

(-->), (/\), (\/), (<@>) :: Expr -> Expr -> Expr
e1 --> e2 = e1 :-> e2
e1 /\ e2  = e1 :/\ e2
e1 \/ e2  = e1 :\/ e2
e1 <@> e2 = e1 :@ e2


{-
  `Axiom axiom e` declares a witness `axiom` of type `e`.

  `Def def ty e` defines `def` to be `e` with type `ty`.

  `Inductive ind ty [Constr c1 e1, ...]` defines an inductive data type
  `ind` of type `ty` with constructors `c1,...` of type `e1,...`.

  `Subtype ty subty` means that `subty` is a subtype of `ty`.
-}

type Name = Text
type Type = Text

data Decl
  = Axiom Name Expr
  | Def Name Expr Expr
  | Theorem Name Expr Expr
  | Inductive Name Expr [Constr]
  | Subtype Type Name
  deriving (Show, Eq)

data Constr
  = Constr Name Expr
  deriving (Show, Eq)
