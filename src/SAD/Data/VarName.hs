module SAD.Data.VarName where

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