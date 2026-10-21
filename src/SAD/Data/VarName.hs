{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.VarName
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.
module SAD.Data.VarName (
  VariableName(..),
  FV,
  unitFV,
  bindVar,
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
import Data.Text qualified as Text

import GHC.Magic (oneShot)

import Isabelle.Position qualified as Position

import SAD.Core.Message (show_position)
import SAD.Export.Presentation


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
  | VarW Text            -- ^ previously starting with w
  | VarEmpty             -- ^ previously ""
  | VarDefault Text      -- ^ everything else
  deriving (Eq, Ord)

isVarHole :: VariableName -> Bool
isVarHole (VarHole _) = True
isVarHole _ = False

instance Show VariableName where
  show = Text.unpack . present

instance Presentation VariableName where
  present (VarConstant s) = "x" <> s
  present (VarHole s) = "?" <> s
  present VarSlot = "!"
  present (VarU s) = "u" <> s
  present (VarHidden n) = "h" <> Text.pack (show n)
  present (VarAssume n) = "i" <> Text.pack (show n)
  present (VarSkolem n) = "o" <> Text.pack (show n)
  present (VarTask s) = "c" <> present s
  present (VarZ s) = "z" <> s
  present (VarW s) = "w" <> s
  present VarEmpty = ""
  present (VarDefault s) = s

data PosVar = PosVar
  { posVarName :: VariableName
  , posVarPosition :: Position.T
  }

instance Show PosVar where
  show = show . posVarName

instance Eq PosVar where
  (==) = (==) `on` posVarName

instance Ord PosVar where
  compare = compare `on` posVarName

instance Presentation PosVar where
  present (PosVar v pos) =
    "(" <> present v <> ", " <> Text.pack (show_position pos) <> ")"

class (Ord a, Presentation a) => IsVar a where
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

bindVar :: Ord a => VariableName -> FV a -> FV a
bindVar v fv = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  runFV fv (Set.insert v boundVars) acc

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
