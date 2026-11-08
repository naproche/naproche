{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.VarName
-- Description : TODO
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
module SAD.Data.VarName (
  VariableName(..),
  FV,
  unitFV,
  excludeVars,
  excludeSet,
  IsVar(..),
  fvToVarSet,
  fvFromVarSet,
  isVarHole,
  PosVar(..)
) where

import Data.Function (on)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)

import GHC.Magic (oneShot)

import Isabelle.Library (make_bytes, show_bytes)
import Isabelle.Position qualified as Position

import SAD.Core.Message (console_position)
import SAD.Export.Pretty


-- These names may not reflect what the constructors are used for..
data VariableName
  = VarConstant Text     -- ^ previously starting with x
  | VarHole Text         -- ^ previously starting with ?
  | VarSlot              -- ^ previously !
  | VarU Text            -- ^ previously starting with u
  | VarHidden Int        -- ^ previously starting with h
  | VarAssume Int        -- ^ previously starting with i
  | VarSkolem Int        -- ^ previously starting with o
  | VarTask VariableName -- ^ previously starting with c
  | VarZ Text            -- ^ previously starting with z
  | VarGlobal Text       -- ^ previously starting with w
  | VarEmpty             -- ^ previously ""
  | VarDefault Text      -- ^ everything else
  deriving (Eq, Ord)

isVarHole :: VariableName -> Bool
isVarHole (VarHole _) = True
isVarHole _ = False

instance Pretty VariableName where
  pretty_print (VarConstant s) = "x" <> make_bytes s
  pretty_print (VarHole s) = "?" <> make_bytes s
  pretty_print VarSlot = "!"
  pretty_print (VarU s) = "u" <> make_bytes s
  pretty_print (VarHidden n) = "h" <> show_bytes n
  pretty_print (VarAssume n) = "i" <> show_bytes n
  pretty_print (VarSkolem n) = "o" <> show_bytes n
  pretty_print (VarTask s) = "c" <> pretty_print s
  pretty_print (VarZ s) = "z" <> make_bytes s
  pretty_print (VarGlobal s) = "w" <> make_bytes s
  pretty_print VarEmpty = ""
  pretty_print (VarDefault s) = make_bytes s

data PosVar = PosVar
  { posVarName :: VariableName
  , posVarPosition :: Position.T
  }

instance Eq PosVar where
  (==) = (==) `on` posVarName

instance Ord PosVar where
  compare = compare `on` posVarName

instance Pretty PosVar where
  pretty_print (PosVar v pos) =
    "(" <> pretty_print v <> ", " <> console_position pos <> ")"

class (Ord a, Pretty a) => IsVar a where
  buildVar :: VariableName -> Position.T -> a

instance IsVar VariableName where
  buildVar = const

instance IsVar PosVar where
  buildVar = PosVar

-- Free variable traversals, see
-- https://www.haskell.org/ghc/blog/20190728-free-variable-traversals.html
-- for explanation

newtype FV a = FV
  { runFV :: Set VariableName  -- bound variable set
          -> Set a  -- the accumulator
          -> Set a  -- the result
  }

instance Monoid (FV a) where
  mempty = FV $ oneShot $ \_ acc -> acc

instance Semigroup (FV a) where
  fv1 <> fv2 = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
    runFV fv1 boundVars (runFV fv2 boundVars acc)

unitFV :: IsVar a => VariableName -> Position.T -> FV a
unitFV v pos = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  if Set.member v boundVars
  then acc
  else Set.insert (buildVar v pos) acc

excludeVars :: Ord a => FV VariableName -> FV a -> FV a
excludeVars fv1 fv2 = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  runFV fv2 (runFV fv1 mempty boundVars) acc

excludeSet :: IsVar a => FV a -> Set VariableName -> FV a
excludeSet fs vs = excludeVars (fvFromVarSet vs) fs

fvFromVarSet :: Ord a => Set a -> FV a
fvFromVarSet vs = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  acc `Set.union` vs

fvToVarSet :: Ord a => FV a -> Set a
fvToVarSet fv = runFV fv mempty mempty
