{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.VarName where

import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Magic (oneShot)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.Builder as Builder
import SAD.Export.Representation

-- These names may not reflect what the constructors are used for..
data VariableName 
  = VarConstant Text   -- ^ previously starting with x
  | VarHole Text       -- ^ previously starting with ?
  | VarNumHole Int     -- ^ previously starting with ?
  | VarSlot            -- ^ previously !
  | VarU Text          -- ^ previously starting with u
  | VarHidden Text     -- ^ previously starting with h
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
  show = Text.unpack . forceBuilder . represent

instance Representation VariableName where
  represent (VarConstant s) = "x" <> (Builder.fromLazyText s)
  represent (VarHole s) = "?" <> (Builder.fromLazyText s)
  represent (VarNumHole s) = "?" <> (Builder.fromString (show s))
  represent (VarSlot) = "!"
  represent (VarU s) = "u" <> (Builder.fromLazyText s)
  represent (VarHidden s) = "h" <> (Builder.fromLazyText s)
  represent (VarAssume s) = "i" <> (Builder.fromString (show s))
  represent (VarSkolem s) = "o" <> (Builder.fromString (show s))
  represent (VarTask s) = "c" <> represent s
  represent (VarZ s) = "z" <> (Builder.fromLazyText s)
  represent (VarW s) = "w" <> (Builder.fromLazyText s)
  represent (VarEmpty) = ""
  represent (VarDefault s) = Builder.fromLazyText s

-- Free variable traversals, see
-- https://www.haskell.org/ghc/blog/20190728-free-variable-traversals.html
-- for explanation

class Monoid a => FreeVarStrategy a where
  unitFV :: VariableName -> a
  bindVar :: VariableName -> a -> a

newtype FV = FV { runFV :: Set VariableName  -- bound variable set
                        -> Set VariableName  -- the accumulator
                        -> Set VariableName  -- the result
                }

instance Monoid FV where
  mempty = FV $ oneShot $ \_ acc -> acc

instance Semigroup FV where
  fv1 <> fv2 = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
    runFV fv1 boundVars (runFV fv2 boundVars acc)

instance FreeVarStrategy FV where
  unitFV v = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
    if Set.member v boundVars
    then acc
    else Set.insert v acc
  bindVar v fv = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
    runFV fv (Set.insert v boundVars) acc

fvToVarSet :: FV -> Set VariableName
fvToVarSet fv = runFV fv mempty mempty

fvToVarList :: FV -> [VariableName]
fvToVarList = Set.toList . fvToVarSet