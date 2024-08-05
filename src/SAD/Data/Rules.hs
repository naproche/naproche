-- |
-- Module      : SAD.Data.Rules
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- TODO: Add description.


module SAD.Data.Rules where

import SAD.Data.Formula (Formula)
import Data.Text.Lazy (Text)


data Rule = Rule {
  left      :: Formula,   -- left side
  right     :: Formula,   -- right side
  condition :: [Formula], -- conditions
  label     :: Text }   -- label

instance Show Rule where
  show rl =
    show (left rl) ++ " = " ++ show (right rl) ++
    ", Cond: " ++ show (condition rl) ++ ", Label: " ++ show (label rl)
