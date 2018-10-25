module Alice.Data.Evaluation where

import Alice.Data.Formula (Formula)


data Eval = EV {
  evTerm :: Formula,  -- the term to be reduced
  evPos  :: Formula,  -- reduction for positive positions
  evNeg  :: Formula,  -- reduction for negative positions
  evCond :: [Formula] -- conditions
  } deriving Show