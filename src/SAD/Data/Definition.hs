-- |
-- Module      : SAD.Data.Definition
-- Description : TODO
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
module SAD.Data.Definition where

import Data.Map (Map)

import SAD.Data.DisTree (DisTree)
import SAD.Data.Formula (Formula, TermId)


data DefType = Signature | Definition
  deriving (Eq)

data DefEntry = DefEntry
  { defGuards :: [Formula]    -- ^ guards of the definitions
  , defFormula :: Formula      -- ^ defining formula
  , defKind :: DefType      -- ^ proper definition or only sig extension
  , defTerm :: Formula      -- ^ defined term
  , defEvidence :: [Formula]    -- ^ evidence from the defining formula
  , defTypeLikes :: [[Formula]]  -- ^ type-likes of the definition
  }

-- | Storage of definitions by term id
type Definitions = Map TermId DefEntry

-- | Yields information as to what can be unfolded.
isDefinition :: DefEntry -> Bool
isDefinition entry = defKind entry == Definition

type Guards = DisTree Bool

data Evaluation = EV {
  evaluationTerm :: Formula,  -- the term to be reduced
  evaluationPositives :: Formula,  -- reduction for positive positions
  evaluationNegatives :: Formula,  -- reduction for negative positions
  evaluationConditions :: [Formula] -- conditions
  }
