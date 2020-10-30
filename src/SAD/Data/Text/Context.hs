module SAD.Data.Text.Context
  ( Context(..)
  , name
  , setFormula
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
import SAD.Data.Formula (Formula, VarName)
import Data.Text (Text)
import Data.Set (Set)

data Context = Context {
  formula        :: Formula,  -- formula of the context
  branch         :: [Block.Block]}  -- branch of the context
  deriving (Eq, Ord, Show)

-- Context utilities

head :: Context -> Block.Block
head  = Prelude.head . branch

tail :: Context -> [Block.Block]
tail  = Prelude.tail . branch

isTopLevel :: Context -> Bool
isTopLevel  = null . tail

isLowLevel :: Context -> Bool
isLowLevel  = not  . isTopLevel

declaredNames :: Context -> Set VarName
declaredNames = Block.declaredNames . head

name :: Context -> Text
name  = Block.name . head

link :: Context -> [Text]
link  = Block.link . head

isAssumption :: Context -> Bool
isAssumption = (==) Assumption . Block.kind . head

setFormula :: Context -> Formula -> Context
setFormula context f = context { formula = f }
