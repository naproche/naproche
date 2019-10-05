module SAD.Data.Definition where

import SAD.Data.Formula (Formula)
import SAD.Data.TermId
import qualified SAD.Data.Structures.DisTree as DT

import Data.Map (Map)

data DefType = Signature | Definition
  deriving (Eq, Show)

data DefEntry = DE
  { guards    :: [Formula]    -- ^ guards of the definitions
  , formula   :: Formula      -- ^ defining formula
  , kind      :: DefType      -- ^ proper definition or only sig extension
  , term      :: Formula      -- ^ defined term
  , evidence  :: [Formula]    -- ^ evidence from the defining formula
  , typeLikes :: [[Formula]]  -- ^ type-likes of the definition
  } deriving Show

-- | Storage of definitions by term id
type Definitions = Map TermId DefEntry

-- | Yields information as to what can be unfolded.
isDefinition :: DefEntry -> Bool
isDefinition entry = kind entry == Definition

type Guards = DT.DisTree Bool

isGuard :: Formula -> Guards -> Bool
isGuard f g = case DT.find f g of [] -> False; (x:_) -> x