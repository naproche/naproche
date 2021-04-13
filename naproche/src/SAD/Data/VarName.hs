{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SAD.Data.VarName
  ( VarName(..)
  , FV, unitFV, bindVar, excludeVars
  , excludeSet
  , IsVar(..)
  , fvToVarSet
  , fvFromVarSet
  , varToIdent
  , PosVar(..)
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Magic (oneShot)
import Data.Text (Text)
import qualified Data.Text as Text
import SAD.Core.SourcePos
import Data.Function (on)

import SAD.Data.Identifier (Ident(..))

-- These names may not reflect what the constructors are used for..
data VarName 
  = VarConstant Text   -- ^ previously starting with x
  | VarHole Text       -- ^ previously starting with ?
  | VarSlot            -- ^ previously !
  | VarHidden Int      -- ^ previously starting with h
  | VarEmpty           -- ^ previously ""
  | VarDefault Text    -- ^ everything else
  deriving (Eq, Ord)

varToIdent :: VarName -> Maybe Ident
varToIdent (VarConstant s) = Just $ NormalIdent s
varToIdent (VarHidden n) = Just $ NormalIdent $ "h" <> (Text.pack (show n))
varToIdent (VarDefault s) = Just $ NormalIdent $ s
varToIdent _ = Nothing

instance Show VarName where
  show (VarConstant s) = Text.unpack s
  show (VarHole s) = "?" <> (Text.unpack s)
  show (VarSlot) = "!"
  show (VarHidden n) = "h" <> show n
  show (VarEmpty) = ""
  show (VarDefault s) = Text.unpack s

data PosVar = PosVar
  { posVarName :: VarName
  , posVarPosition :: SourcePos
  } deriving (Show)

instance Eq PosVar where
  (==) = (==) `on` posVarName

instance Ord PosVar where
  compare = compare `on` posVarName

class Ord a => IsVar a where
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