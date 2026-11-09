{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.Tag
-- Description : TODO
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
module SAD.Data.Tag where

import SAD.Export.Pretty

data Tag =
  Dig | DigMultiSubject | DigMultiPairwise | HeadTerm |
  InductionHypothesis | CaseHypothesis | EqualityChain |
  -- Tags to mark certain parts of map definitions
  GenericMark | Evaluation | Condition | Defined | Domain | Replacement |
  -- Tags to mark parts in map proof tasks
  DomainTask | ExistenceTask | UniquenessTask | ChoiceTask
  deriving (Eq, Ord)

instance Pretty Tag where
  pretty_print Dig = "dig"
  pretty_print DigMultiSubject = "dig_multi_subject"
  pretty_print DigMultiPairwise = "dig_multi_pairwise"
  pretty_print HeadTerm = "head_term"
  pretty_print InductionHypothesis = "induction_hypothesis"
  pretty_print CaseHypothesis = "case_hypothesis"
  pretty_print EqualityChain = "equality_chain"
  pretty_print GenericMark = "generic_mark"
  pretty_print Evaluation = "evaluation"
  pretty_print Condition = "condition"
  pretty_print Defined = "defined"
  pretty_print Domain = "domain"
  pretty_print Replacement = "replacement"
  pretty_print DomainTask = "domain_task"
  pretty_print ExistenceTask = "existence_task"
  pretty_print UniquenessTask = "uniqueness_task"
  pretty_print ChoiceTask = "choice_task"

-- | whether a Tag marks a part in a map proof task
fnTag :: Tag -> Bool
fnTag DomainTask = True; fnTag ChoiceTask = True
fnTag ExistenceTask = True; fnTag UniquenessTask = True
fnTag _ = False
