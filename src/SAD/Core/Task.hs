{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Create proof tasks from statements.
-- This will evaluate tactics and create the necessary
-- statements for the prover.

module SAD.Core.Task (Hypothesis(..), Task(..), taskFile, generateTasks) where

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
import SAD.Core.SourcePos (SourcePos, sourceFile)
import qualified Data.Set as Set

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
  , byContradiction :: Bool -- ^ eprover can detect contradictory axioms
    -- and so we store whether we are in a proof by contradiction (where contradictory axioms are fine).
  , taskPos :: SourcePos
  } deriving (Eq, Ord, Generic)
instance Hashable Task
instance Binary Task

taskFile :: Task -> FilePath
taskFile = sourceFile . taskPos

instance Pretty Hypothesis where
  pretty (Given n t) = n <> " : " <> pretty t
  pretty (Typing n t) = pretty n <> " : " <> pretty t

instance Pretty Task where
  pretty (Task hypo c h n bc _) = 
    "Goal \"" <> n <> "\": " <> pretty c <> " " <> inParens h 
    <> (if bc then " by contradiction" else "") <> "\n"
    <> Text.unlines (pretty <$> hypo)

-- | Generate tasks from the given proofs under the hypothesis that were assumed at this point.
-- When handling subclaims we assume we are not in a proof by contradiction.
-- That seems consistent with normal mathematical practice.
generateFromProof :: Text -> SourcePos -> [Hypothesis] -> ProofBlock -> [Task]
generateFromProof topname topPos hypo (Proving prf topclaim tophints)
  = concat $ finalize $ mapAccumL go (hypo, False) prf
  where
    finalize ((h', isContra), ts) = ts ++ [[Task h' topclaim tophints topname isContra topPos]]

    go (hypo, isContra) (Located n _ p) = case p of
      Intro v typ -> (((Typing (TermVar v) (Pred [] (InType typ))):hypo, isContra), [])
      Assume t -> (((Given n t):hypo, isContra), [])
      Subclaim t prf -> (((Given n t):hypo, isContra), generateFromProof n topPos hypo prf)
      Cases [] -> ((hypo, isContra), [])
      Cases cs ->
        let cases = concatMap (\(c, p) -> generateFromProof "case" topPos (Given "case" c:hypo) p) cs
            claim = foldl1 (\a b -> App Or [a, b]) $ map (\(c, p) -> App Imp [c, asTerm p]) cs
        in (((Given n claim):hypo, isContra), cases)
      TerminalCases [] -> ((hypo, isContra), [])
      TerminalCases cs ->
        let cases = concatMap (\(c, p) -> generateFromProof "case" topPos (Given "case" c:hypo) p) cs
            final = foldl1 (\a b -> App Or [a, b]) (map fst cs)
        in ((hypo, isContra), cases ++ [Task hypo final [] n isContra topPos])
      ByContradiction goal -> (((Given n (simp $ App Not [goal])):hypo, True), [])
      Choose vs t prf -> -- TODO: Check if this is correct if the bound variable is a TermVar in the statement...
        let ts = map (\(v, typ) -> Typing (TermVar v) (Pred [] (InType typ))) vs
        in (((Given n t) : ts ++ hypo, isContra), generateFromProof n topPos hypo prf)

-- | Turn a proof block back into a term by unrolling all chooses, intros and assumptions.
-- This might bind variables that are unused in the term and a future implementation should
-- make sure we don't add junk.
-- Danger: This function should not be used in the presence of the ByContradiction tactic.
asTerm :: PrfBlock Identity () -> Term Identity ()
asTerm (Proving prfs trm _) = unrollTermVars $ case prfs of
  [] -> trm
  ((Located _ _ (Intro v typ)):ps) -> Forall v (Identity typ) $ asTerm (Proving ps trm [])
  ((Located _ _ (Assume a)):ps) -> App Imp [a, asTerm (Proving ps trm [])]
  ((Located _ _ (Choose vs hypo _)):ps) -> foldr (\(v, typ) t -> Exists v (Identity typ) t)
    (App Imp [hypo, asTerm (Proving ps trm [])]) vs
  ((Located _ _ (ByContradiction goal)):_) -> goal
  (_:ps) -> asTerm (Proving ps trm [])

unrollTermVars :: Term Identity () -> Term Identity ()
unrollTermVars = go mempty
  where
    go vars = \case
      Forall v m t -> Forall v m (go (Set.insert v vars) t)
      Exists v m t -> Exists v m (go (Set.insert v vars) t)
      Class v m t -> Class v m (go (Set.insert v vars) t)
      App (OpTrm (TermVar v)) [] | v `Set.member` vars -> Var v
      App op as -> App op (go vars <$> as)
      Tag () t -> Tag () $ go vars t
      Var v -> Var v

generateTasks :: [Statement] -> [Task]
generateTasks = concat . snd . mapAccumL go []
  where
    go hypo (Located n pos term) = case term of
      IntroSort t -> ((Typing t Sort):hypo, [])
      Predicate n ts t -> ((Typing n (Pred ts t)):hypo, [])
      Axiom t -> ((Given n t):hypo, [])
      Claim t prf -> ((Given n t):hypo, generateFromProof n pos hypo prf)
      Coercion n f t -> ((Typing n (Pred [Signature f] (InType (Signature t)))):hypo, [])