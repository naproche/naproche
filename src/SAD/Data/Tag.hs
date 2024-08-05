-- |
-- Module      : SAD.Data.Tag
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- TODO: Add description.


module SAD.Data.Tag where

data Tag =
  Dig | DigMultiSubject | DigMultiPairwise | HeadTerm |
  InductionHypothesis | CaseHypothesis | EqualityChain |
  -- Tags to mark certain parts of map definitions
  GenericMark | Evaluation | Condition | Defined | Domain | Replacement |
  -- Tags to mark parts in map proof tasks
  DomainTask | ExistenceTask | UniquenessTask | ChoiceTask
  deriving (Eq, Ord, Show)

-- | whether a Tag marks a part in a map proof task
fnTag :: Tag -> Bool
fnTag DomainTask    = True; fnTag ChoiceTask     = True
fnTag ExistenceTask = True; fnTag UniquenessTask = True
fnTag _   = False
