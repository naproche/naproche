-- |
-- Module      : SAD.Data.Text.Context
-- Description : TODO
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
module SAD.Data.Text.Context (
  Context(..),
  MRule(..),
  name,
  setFormula,
  isLowLevel,
  link,
  head,
  isAssumption,
  declaredNames,
  isTopLevel
) where

import Data.Set (Set)

import Isabelle.Bytes (Bytes)

import Prelude hiding (head, tail)
import Prelude qualified (head, tail)

import SAD.Data.Formula (Formula, VariableName)
import SAD.Data.Text.Block (Section(..))
import SAD.Data.Text.Block qualified as Block


data Context = Context {
  formula :: Formula,  -- formula of the context
  branch :: [Block.Block],  -- branch of the context
  mesonRules :: [MRule]}  -- MESON rules extracted from the formula

data MRule = MR
  { assumption :: [Formula] -- assumptions of the rule
  , conclusion :: Formula   -- conclusion of the rule
  } deriving (Eq, Ord)



-- Context utilities

head :: Context -> Block.Block
head = Prelude.head . branch

tail :: Context -> [Block.Block]
tail = Prelude.tail . branch

isTopLevel :: Context -> Bool
isTopLevel = null . tail

isLowLevel :: Context -> Bool
isLowLevel = not  . isTopLevel

declaredNames :: Context -> Set VariableName
declaredNames = Block.declaredNames . head

name :: Context -> Bytes
name = Block.name . head

link :: Context -> [Bytes]
link = Block.link . head

isAssumption :: Context -> Bool
isAssumption = (==) Assumption . Block.kind . head

setFormula :: Context -> Formula -> Context
setFormula context f = context { formula = f }

