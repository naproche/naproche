-- |
-- Module      : SAD.Data.Definition
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- TODO: Add description.


module SAD.Data.Definition where

import Data.Map (Map)

import SAD.Data.Formula (Formula, TermId)
import SAD.Data.Structures.DisTree (DisTree)
import SAD.Data.Structures.DisTree qualified as DisTree


data DefType = Signature | Definition
  deriving (Eq, Show)

data DefEntry = DefEntry
  { defGuards    :: [Formula]    -- ^ guards of the definitions
  , defFormula   :: Formula      -- ^ defining formula
  , defKind      :: DefType      -- ^ proper definition or only sig extension
  , defTerm      :: Formula      -- ^ defined term
  , defEvidence  :: [Formula]    -- ^ evidence from the defining formula
  , defTypeLikes :: [[Formula]]  -- ^ type-likes of the definition
  } deriving Show

-- | Storage of definitions by term id
type Definitions = Map TermId DefEntry

-- | Yields information as to what can be unfolded.
isDefinition :: DefEntry -> Bool
isDefinition entry = defKind entry == Definition

type Guards = DisTree Bool

isGuard :: Formula -> Guards -> Bool
isGuard f g = case DisTree.find f g of [] -> False; (x:_) -> x

data Evaluation = EV {
  evaluationTerm       :: Formula,  -- the term to be reduced
  evaluationPositives  :: Formula,  -- reduction for positive positions
  evaluationNegatives  :: Formula,  -- reduction for negative positions
  evaluationConditions :: [Formula] -- conditions
  } deriving Show
