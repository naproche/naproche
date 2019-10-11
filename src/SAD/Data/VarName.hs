module SAD.Data.VarName where

import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Magic (oneShot)

-- These names may not reflect what the constructors are used for..
data VariableName 
  = VarConstant String   -- ^ previously starting with x
  | VarHole String       -- ^ previously starting with ?
  | VarSlot              -- ^ previously !
  | VarU String          -- ^ previously starting with u
  | VarHidden String     -- ^ previously starting with h
  | VarAssume String     -- ^ previously starting with i
  | VarSkolem String     -- ^ previously starting with o
  | VarTask VariableName -- ^ previously starting with c
  | VarZ String          -- ^ previously starting with z
  | VarW String          -- ^ previously starting with w
  | VarEmpty             -- ^ previously ""
  | VarDefault String    -- ^ everything else
  deriving (Eq, Ord)

isHole :: VariableName -> Bool
isHole (VarHole _) = True
isHole _ = False

-- SAD.ForTheL.Pattern.avr and SAD.Export.DFG.* depend on this behaviour.
instance Show VariableName where
  show (VarConstant s) = 'x' : s
  show (VarHole s) = '?' : s
  show (VarSlot) = "!"
  show (VarU s) = 'u' : s
  show (VarHidden s) = 'h' : s
  show (VarAssume s) = 'i' : s
  show (VarSkolem s) = 'o' : s
  show (VarTask s) = 'c' : show s
  show (VarZ s) = 'z' : s
  show (VarW s) = 'w' : s
  show (VarEmpty) = ""
  show (VarDefault s) = s

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