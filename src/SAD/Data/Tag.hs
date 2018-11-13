module SAD.Data.Tag where

data Tag =
  Dig | DigMultiSubject | DigMultiPairwise | HeadTerm | 
  InductionHypothesis | CaseHypothesis | EqualityChain |
  -- Tags to mark certain parts of function definitions
  GenericMark | Evaluation | Condition | Defined | Domain | Replacement |
  -- Tags to mark parts in function proof tasks
  DomainTask | ExistenceTask | UniquenessTask | ChoiceTask
  deriving (Eq, Show)

{- whether a Tag marks a part in a function proof task -}
fnTag :: Tag -> Bool
fnTag DomainTask    = True; fnTag ChoiceTask     = True
fnTag ExistenceTask = True; fnTag UniquenessTask = True
fnTag _   = False