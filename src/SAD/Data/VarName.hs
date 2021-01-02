{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}

module SAD.Data.VarName
  ( VarName(..)
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
import SAD.Core.Pretty
import SAD.Core.SourcePos
import Data.Function (on)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)

-- These names may not reflect what the constructors are used for..
data VarName 
  = VarConstant Text   -- ^ previously starting with x
  | VarHole Text       -- ^ previously starting with ?
  | VarSlot            -- ^ previously !
  | VarU Text          -- ^ previously starting with u
  | VarHidden Int      -- ^ previously starting with h
  | VarAssume Int      -- ^ previously starting with i
  | VarSkolem Int      -- ^ previously starting with o
  | VarTask VarName    -- ^ previously starting with c
  | VarZ Text          -- ^ previously starting with z
  | VarW Text          -- ^ previously starting with w
  | VarF Int           -- ^ for function outputs
  | VarEmpty           -- ^ previously ""
  | VarDefault Text    -- ^ everything else
  deriving (Eq, Ord, Show, Read, Generic)
instance Hashable VarName

isHole :: VarName -> Bool
isHole (VarHole _) = True
isHole _ = False

instance Pretty VarName where
  pretty (VarConstant s) = s
  pretty (VarHole s) = "?" <> ( s)
  pretty (VarSlot) = "!"
  pretty (VarU s) = "u" <> ( s)
  pretty (VarHidden n) = "h" <> (Text.pack (show n))
  pretty (VarAssume n) = "i" <> (Text.pack (show n))
  pretty (VarSkolem n) = "o" <> (Text.pack (show n))
  pretty (VarTask s) = "c" <> pretty s
  pretty (VarZ s) = "z" <> ( s)
  pretty (VarW s) = "w" <> ( s)
  pretty (VarF s) = "out_" <> (Text.pack (show s))
  pretty (VarEmpty) = ""
  pretty (VarDefault s) =  s

data PosVar = PosVar
  { posVarName :: VarName
  , posVarPosition :: SourcePos
  } deriving (Show)

instance Eq PosVar where
  (==) = (==) `on` posVarName

instance Ord PosVar where
  compare = compare `on` posVarName

instance Pretty PosVar where
  pretty (PosVar v p) = "(" <> pretty v <> ", " <> Text.pack (show p) <> ")"

class (Ord a, Pretty a) => IsVar a where
  buildVar :: VarName -> SourcePos -> a

instance IsVar VarName where
  buildVar = const

instance IsVar PosVar where
  buildVar = PosVar

-- Free variable traversals, see
-- https://www.haskell.org/ghc/blog/20190728-free-variable-traversals.html
-- for explanation

newtype FV a = FV
  { runFV :: Set VarName  -- bound variable set
          -> Set a  -- the accumulator
          -> Set a  -- the result
  }

instance Monoid (FV a) where
  mempty = FV $ oneShot $ \_ acc -> acc

instance Semigroup (FV a) where
  fv1 <> fv2 = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
    runFV fv1 boundVars (runFV fv2 boundVars acc)

unitFV :: IsVar a => VarName -> SourcePos -> FV a
unitFV v s = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  if Set.member v boundVars
  then acc
  else Set.insert (buildVar v s) acc

bindVar :: Ord a => VarName -> FV a -> FV a
bindVar v fv = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  runFV fv (Set.insert v boundVars) acc

excludeVars :: Ord a => FV VarName -> FV a -> FV a
excludeVars fv1 fv2 = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  runFV fv2 (runFV fv1 mempty boundVars) acc

excludeSet :: IsVar a => FV a -> Set VarName -> FV a
excludeSet fs vs = excludeVars (fvFromVarSet id vs) fs

fvFromVarSet :: Ord a => (a -> VarName) -> Set a -> FV a
fvFromVarSet f vs = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  acc `Set.union` (Set.filter (\a -> Set.notMember (f a) boundVars) vs)

fvToVarSet :: Ord a => FV a -> Set a
fvToVarSet fv = runFV fv mempty mempty