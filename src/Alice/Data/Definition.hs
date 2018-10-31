module Alice.Data.Definition where

import Alice.Data.Formula (Formula)

import Data.IntMap (IntMap)

data DefType = Signature | Definition deriving (Eq, Show)
data DefEntry = DE {
  guards    :: [Formula],   -- guards of the definitions
  formula   :: Formula,     -- defining formula
  kind      :: DefType,     -- proper definition or only sig extension
  term      :: Formula,     -- defined term
  evidence  :: [Formula],   -- evidence from the defining formula
  typeLikes :: [[Formula]]  -- type-likes of the definition
  } deriving Show

{- yields information as to what can be unfolded -}
isDefinition :: DefEntry -> Bool
isDefinition = (==) Definition . kind

{- storage of definitions by term id -}
type Definitions = IntMap DefEntry
