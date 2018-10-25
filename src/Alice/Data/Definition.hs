module Alice.Data.Definition where

import Alice.Data.Formula (Formula)

import Data.IntMap (IntMap)

data DefType = Signature | Definition deriving (Eq, Show)
data DefEntry = DE {
  dfGrds :: [Formula],   -- guards of the definitions
  dfForm :: Formula,     -- defining formula
  dfType :: DefType,     -- proper definition or only sig extension
  dfTerm :: Formula,     -- defined term
  dfEvid :: [Formula],   -- evidence from the defining formula
  dfTplk :: [[Formula]]  -- type-likes of the definition
  } deriving Show

{- yields information as to what can be unfolded -}
dfSign :: DefEntry -> Bool
dfSign df = dfSign' $ dfType df
  where
    dfSign' Definition = True
    dfSign' _ = False

{- storage of definitions by term id -}
type Definitions = IntMap DefEntry
