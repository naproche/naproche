module SAD.Data.Text.Context 
  ( Context(..)
  , MRule(..)
  , name
  , setForm
  , isLowLevel
  , link
  , head
  , isAssumption
  , declaredNames
  , isTopLevel
  ) where

import Prelude hiding (head, tail)
import qualified Prelude as Prelude (head, tail)
import SAD.Data.Text.Block (Section(..))
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Formula (Formula)
import SAD.Data.VarName

data Context = Context {
  formula        :: Formula,  -- formula of the context
  branch         :: [Block.Block],  -- branch of the context
  mesonRules     :: [MRule],  -- MESON rules extracted from the formula
  reducedFormula :: Formula } -- ontologically reduced formula
  deriving (Eq, Ord, Show)

data MRule = MR 
  { assumption :: [Formula] -- assumptions of the rule
  , conclusion :: Formula   -- conclusion of the rule
  } deriving (Eq, Ord, Show)



-- Context utilities

head :: Context -> Block.Block
head  = Prelude.head . branch

tail :: Context -> [Block.Block]
tail  = Prelude.tail . branch

isTopLevel :: Context -> Bool
isTopLevel  = null . tail

isLowLevel :: Context -> Bool
isLowLevel  = not  . isTopLevel

declaredNames :: Context -> [VariableName]
declaredNames = Block.declaredNames . head

name :: Context -> String
name  = Block.name . head

link :: Context -> [String]
link  = Block.link . head

isAssumption :: Context -> Bool
isAssumption = (==) Assumption . Block.kind . head

setForm :: Context -> Formula -> Context
setForm context f = context { formula = f }