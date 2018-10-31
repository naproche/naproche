module Alice.Data.Evaluation where

import Alice.Data.Formula (Formula)


data Evaluation = EV {
  term       :: Formula,  -- the term to be reduced
  positives  :: Formula,  -- reduction for positive positions
  negatives  :: Formula,  -- reduction for negative positions
  conditions :: [Formula] -- conditions
  } deriving Show