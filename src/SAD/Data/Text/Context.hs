-- |
-- Module      : SAD.Data.Text.Context
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE OverloadedStrings #-}


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
  isTopLevel,
  output
) where

import Prelude hiding (head, tail)
import Prelude qualified (head, tail)
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.Set (Set)

import SAD.Data.Text.Block (Section(..))
import SAD.Data.Text.Block qualified as Block
import SAD.Data.Formula (Formula, VariableName)
import SAD.Export.TPTP qualified as TPTP


data Context = Context {
  formula        :: Formula,  -- formula of the context
  branch         :: [Block.Block],  -- branch of the context
  mesonRules     :: [MRule]}  -- MESON rules extracted from the formula
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

declaredNames :: Context -> Set VariableName
declaredNames = Block.declaredNames . head

name :: Context -> Text
name  = Block.name . head

link :: Context -> [Text]
link  = Block.link . head

isAssumption :: Context -> Bool
isAssumption = (==) Assumption . Block.kind . head

setFormula :: Context -> Formula -> Context
setFormula context f = context { formula = f }


-- TPTP rendering

output :: [Context] -> Context -> Text
output contexts goal =
  Text.unlines (map (tptpForm TPTP.Hypothesis) $ reverse contexts)
  <> "\n" <> tptpForm TPTP.Conjecture goal

-- Formula print
tptpForm :: TPTP.Role -> Context -> Text
tptpForm role (Context formula (Block.Block { Block.name = name } : _) _) =
  TPTP.renderLogicFormula name role formula
tptpForm _ _ = ""
