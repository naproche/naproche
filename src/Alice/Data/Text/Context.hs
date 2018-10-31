module Alice.Data.Text.Context where

import Prelude hiding (head, tail)
import qualified Prelude as Prelude (head, tail)
import Alice.Data.Text.Block (Section(..))
import qualified Alice.Data.Text.Block as Block
import Alice.Data.Formula (Formula)

data Context = Context { 
  formula        :: Formula,  -- formula of the context
  branch         :: [Block.Block],  -- branch of the context
  mesonRules     :: [MRule],  -- MESON rules extracted from the formula
  reducedFormula :: Formula } -- ontologically reduced formula

data MRule = MR { 
  assumption :: [Formula], -- assumptions of the rule
  conclusion :: Formula } -- conclusion of the rule
  deriving Show



-- Context utilities

head  = Prelude.head . branch
tail  = Prelude.tail . branch
isTopLevel  = null . tail
isLowLevel  = not  . isTopLevel

declaredVariables  = Block.declaredVariables . head
name  = Block.name . head
link  = Block.link . head



isAssumption = (==) Assumption . Block.kind . head

setForm :: Context -> Formula -> Context
setForm context f = context { formula = f }

setRedu :: Context -> Formula -> Context
setRedu context f = context { reducedFormula = f }


instance Show Context where
  show = show . formula