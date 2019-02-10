module SAD.Data.Definition where

import SAD.Data.Formula (Formula)
import qualified SAD.Data.Structures.DisTree as DT

import Data.IntMap (IntMap)
import Data.Maybe

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


--- guards


type Guards = DT.DisTree Bool

isGuard :: Formula -> Guards -> Bool
isGuard f = head . fromMaybe [False] . DT.lookup f
