{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Create proof tasks from statements.
-- This will evaluate tactics and create the necessary
-- statements for the prover.

module SAD.Core.Task (Hypothesis(..), Task(..), generateTasks) where

import Data.List
import Data.Functor.Identity
import Data.Text (Text)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import Data.Binary (Binary)

import SAD.Core.Typed
import SAD.Data.Terms
import SAD.Core.Pretty
import qualified Data.Text as Text
import SAD.Helpers (inParens)
import SAD.Core.SourcePos (sourceFile)

data Hypothesis
  = Given Text (Term Identity ())
  | Typing TermName Type
  deriving (Eq, Ord, Show, Read, Generic)
instance Hashable Hypothesis
instance Binary Hypothesis

data Task = Task 
  { hypothesis :: [Hypothesis] -- ^ from newest to oldest
  , conjecture :: (Term Identity ())
  , hints :: [Text] -- ^ helpful lemmata
  , taskName :: Text
  , taskFile :: Text -- ^ the file where the task was defined
  , byContradiction :: Bool -- ^ eprover can detect contradictory axioms
    -- and so we store whether we are in a proof by contradiction (where contradictory axioms are fine).
  } deriving (Eq, Ord, Show, Read, Generic)
instance Hashable Task
instance Binary Task

instance Pretty Hypothesis where
  pretty (Given n t) = n <> " : " <> pretty t
  pretty (Typing n t) = pretty n <> " : " <> pretty t

instance Pretty Task where
  pretty (Task hypo c h n _ bc) = 
    "Goal \"" <> n <> "\": " <> pretty c <> " " <> inParens h 
    <> (if bc then " by contradiction" else "") <> "\n"
    <> Text.unlines (pretty <$> hypo)

-- | Generate tasks from the given proofs under the hypothesis that were assumed at this point.
-- When handling subclaims we forget if we are in a proof by contradiction and assume we aren't.
-- That seems consistent with normal mathematical practice.
generateFromProof :: Text -> Text -> [Hypothesis] -> ProofBlock -> [Task]
generateFromProof topname topfile hypo (Proving prf topclaim tophints)
  = concat $ finalize $ mapAccumL go (hypo, False) prf
  where
    finalize ((h', isContra), ts) = ts ++ [[Task h' topclaim tophints topname topfile isContra]]

    go (hypo, isContra) (Located n _ p) = case p of
      Intro v typ -> (((Typing (TermVar v) (Pred [] (InType typ))):hypo, isContra), [])
      Assume t -> (((Given n t):hypo, isContra), [])
      Subclaim t prf -> (((Given n t):hypo, isContra), generateFromProof n topfile hypo prf)
      Cases [] -> ((hypo, isContra), [])
      Cases cs ->
        let cases = concatMap (\(c, p) -> generateFromProof "case" topfile (Given "case" c:hypo) p) cs
            claim = foldl1 (\a b -> App Or [a, b]) $ map (\(c, p) -> App Imp [c, asTerm p]) cs
        in (((Given n claim):hypo, isContra), cases)
      TerminalCases [] -> ((hypo, isContra), [])
      TerminalCases cs ->
        let cases = concatMap (\(c, p) -> generateFromProof "case" topfile (Given "case" c:hypo) p) cs
            final = foldl1 (\a b -> App Or [a, b]) (map fst cs)
        in ((hypo, isContra), cases ++ [Task hypo final [] n topfile isContra])
      ByContradiction goal -> (((Given n (simp $ App Not [goal])):hypo, True), [])
      Choose vs t prf ->
        let ts = map (\(v, typ) -> Typing (TermVar v) (Pred [] (InType typ))) vs
        in (((Given n t) : ts ++ hypo, isContra), generateFromProof n topfile hypo prf)

-- | Turn a proof block back into a term by unrolling all chooses, intros and assumptions.
-- This might bind variables that are unused in the term and a future implementation should
-- make sure we don't add junk.
-- Danger: This function should not be used in the presence of the ByContradiction tactic.
asTerm :: PrfBlock Identity () -> Term Identity ()
asTerm (Proving prfs trm _) = case prfs of
  [] -> trm
  ((Located _ _ (Intro v typ)):ps) -> Forall v (Identity typ) $ asTerm (Proving ps trm [])
  ((Located _ _ (Assume a)):ps) -> App Imp [a, asTerm (Proving ps trm [])]
  ((Located _ _ (Choose vs hypo _)):ps) -> foldr (\(v, typ) t -> Exists v (Identity typ) t)
    (App Imp [hypo, asTerm (Proving ps trm [])]) vs
  ((Located _ _ (ByContradiction goal)):_) -> goal
  (_:ps) -> asTerm (Proving ps trm [])

generateTasks :: [Statement] -> [Task]
generateTasks = concat . snd . mapAccumL go []
  where
    go hypo (Located n pos term) = case term of
      IntroSort t -> ((Typing t Sort):hypo, [])
      Predicate n ts t -> ((Typing n (Pred ts t)):hypo, [])
      Axiom t -> ((Given n t):hypo, [])
      Claim t prf -> ((Given n t):hypo, generateFromProof n (sourceFile pos) hypo prf)
      Coercion n f t -> ((Typing n (Pred [Signature f] (InType (Signature t)))):hypo, [])