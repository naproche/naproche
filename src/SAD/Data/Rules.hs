module SAD.Data.Rules where

import SAD.Data.Formula (Formula)

data Rule = Rule {
  left      :: Formula,   -- left side
  right     :: Formula,   -- right side
  condition :: [Formula], -- conditions
  label     :: String }   -- label

instance Show Rule where
  show rl = 
    show (left rl) ++ " = " ++ show (right rl) ++
    ", Cond: " ++ show (condition rl) ++ ", Label: " ++ show (label rl)

printrules :: [Rule] -> String
printrules = unlines . map show