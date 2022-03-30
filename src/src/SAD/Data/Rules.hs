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
