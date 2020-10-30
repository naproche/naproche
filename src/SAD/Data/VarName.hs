{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SAD.Data.VarName
  ( VariableName(..)
  , FV, unitFV, bindVar, excludeVars
  , excludeSet
  , IsVar(..)
  , fvToVarSet
  , fvFromVarSet
  , isHole
  , PosVar(..)
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Magic (oneShot)
import Data.Text (Text)
import qualified Data.Text as Text
import SAD.Export.Representation
import SAD.Core.SourcePos
import Data.Function (on)

-- These names may not reflect what the constructors are used for..
data VariableName 
  = VarConstant Text   -- ^ previously starting with x
  | VarHole Text       -- ^ previously starting with ?
  | VarSlot            -- ^ previously !
  | VarU Text          -- ^ previously starting with u
  | VarHidden Int      -- ^ previously starting with h
  | VarAssume Int      -- ^ previously starting with i
  | VarSkolem Int      -- ^ previously starting with o
  | VarTask VariableName -- ^ previously starting with c
  | VarZ Text          -- ^ previously starting with z
  | VarW Text          -- ^ previously starting with w
  | VarEmpty             -- ^ previously ""
  | VarDefault Text    -- ^ everything else
  deriving (Eq, Ord)

isHole :: VariableName -> Bool
isHole (VarHole _) = True
isHole _ = False

instance Show VariableName where
  show = Text.unpack . represent

instance Representation VariableName where
  represent (VarConstant s) = "x" <> ( s)
  represent (VarHole s) = "?" <> ( s)
  represent (VarSlot) = "!"
  represent (VarU s) = "u" <> ( s)
  represent (VarHidden n) = "h" <> (Text.pack (show n))
  represent (VarAssume n) = "i" <> (Text.pack (show n))
  represent (VarSkolem n) = "o" <> (Text.pack (show n))
  represent (VarTask s) = "c" <> represent s
  represent (VarZ s) = "z" <> ( s)
  represent (VarW s) = "w" <> ( s)
  represent (VarEmpty) = ""
  represent (VarDefault s) =  s

data PosVar = PosVar
  { posVarName :: VariableName
  , posVarPosition :: SourcePos
  } deriving (Show)

instance Eq PosVar where
  (==) = (==) `on` posVarName

instance Ord PosVar where
  compare = compare `on` posVarName

instance Representation PosVar where
  represent (PosVar v p) = "(" <> represent v <> ", " <> Text.pack (show p) <> ")"

class (Ord a, Representation a) => IsVar a where
  buildVar :: VariableName -> SourcePos -> a

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

unitFV :: IsVar a => VariableName -> SourcePos -> FV a
unitFV v s = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  if Set.member v boundVars
  then acc
  else Set.insert (buildVar v s) acc

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