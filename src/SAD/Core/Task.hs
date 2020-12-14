{-# LANGUAGE OverloadedStrings #-}

-- | Create proof tasks from statements.
-- This will evaluate tactics and create the necessary
-- statements for the prover.

module SAD.Core.Task where

import Data.List
import Data.Functor.Identity
import Data.Text (Text)

import SAD.Core.Typed
import SAD.Data.Terms

data Hypothesis
  = Given Text (Term Identity ())
  | Typing TermName Type
  deriving (Eq, Ord, Show)

data Task = Task 
  { hypothesis :: [Hypothesis] -- ^ from newest to oldest
  , conjecture :: (Term Identity ())
  , hints :: [Text] -- ^ helpful lemmata
  , taskName :: Text
  , byContradiction :: Bool
  } deriving (Eq, Ord, Show)

generateFromProof :: Task -> [Proof] -> [Task]
generateFromProof tsk [] = [tsk]
generateFromProof (Task hypo conj conjHints name contra) prf 
  = concat $ finalize $ mapAccumL go hypo prf
  where
    -- TODO: This should bind let-introduced variables
    -- with forall quantifiers in h'
    finalize (h', ts) = ts ++ [[Task h' conj conjHints name contra]]
    
    go hypo (Located n _ p) = case p of
      Subclaim t hints prf -> ((Given n t):hypo, 
        generateFromProof (Task hypo t hints n contra) prf)
      Cases [] -> (hypo, [])
      Cases cs ->
        let cases = concatMap (\(c, p) -> concat $ snd 
              $ mapAccumL go (Given "case" c:hypo) p) cs
            final = foldl1 (\a b -> App Or [a, b]) (map fst cs)
        in (hypo, cases ++ [Task hypo final [] n contra])
      ByContradiction t prf -> ((Given n t):hypo,
        generateFromProof (Task (Given n (App Not [t]):hypo) (App Bot []) [] n True) prf)
      Choose vs t hints prf -> ((Given n t):hypo,
        generateFromProof (Task hypo t hints n contra) prf)
      t -> error $ "Not implemented tactic: " ++ show t

generateTasks :: [Statement] -> [Task]
generateTasks = concat . snd . mapAccumL go []
  where
    go hypo (Located n _ term) = case term of
      IntroSort t -> ((Typing t Sort):hypo, [])
      Predicate n ts t -> ((Typing n (Pred ts t)):hypo, [])
      Axiom t -> ((Given n t):hypo, [])
      Claim t hints prf -> ((Given n t):hypo, 
        generateFromProof (Task hypo t hints n False) prf)
      Coercion n f t -> ((Typing n (Pred [Signature f] (InType (Signature t)))):hypo, [])