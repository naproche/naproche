module Alice.Data.Rules where

import Alice.Data.Formula (Formula)

data Rule = Rule {
  rlLeft :: Formula,   -- left side
  rlRght :: Formula,   -- right side
  rlCond :: [Formula], -- conditions
  rlLabl :: String }   -- label

instance Show Rule where
  show rl = 
    show (rlLeft rl) ++ " = " ++ show (rlRght rl) ++
    ", Cond: " ++ show (rlCond rl) ++ ", Label: " ++ show (rlLabl rl)

printrules :: [Rule] -> String
printrules = unlines . map show