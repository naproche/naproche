{-# LANGUAGE OverloadedStrings #-}

-- | Create proof tasks from statements.
-- This will evaluate tactics and create the necessary
-- statements for the prover.
-- Is a statement like $1 / 0 = 1 / 0$ true?
-- An ATP would say yes, but a mathematician would say no.
-- Therefore we check preconditions of definitions when they are used.
-- This is called ontological checking.

module SAD.Core.Tactic (generateTasks) where

import Prelude hiding (error)
import qualified Prelude
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String
import Control.Monad.Identity
import Control.Monad.State
import Data.List
import Data.Text (Text)

import SAD.Core.Typed
import SAD.Core.SourcePos (SourcePos)
import SAD.Core.Task
import qualified Isabelle.Naproche as Naproche
import SAD.Core.Message
import SAD.Core.Cache (CacheStorage, store)
import SAD.Core.Prove

failWithMessage :: (Show t, CacheStorage m, Comm m) => Located (Stmt Identity ()) -> Term Identity t -> ProveT m a
failWithMessage (Located _ pos stmt) def = do
  c <- proveCache <$> get
  lift $ store c
  w <- lift $ textFieldWidth
  lift $ error Naproche.origin_reasoner pos $ renderString $ layoutSmart
    (defaultLayoutOptions { layoutPageWidth = AvailablePerLine w 1.0 })
    $  "\nIn the block:\n\n" <> pretty stmt
    <> "\nyou use the definition:\n\n" <> pretty def
    <> "\n\nbut a precondition is not met." 

-- TODO: Ontological checking support!

generateTask :: Bool -> Term Identity () -> [Hypothesis] -> Located (Prf Identity ()) -> [Task]
generateTask isContra goal hypo (Located n p tactic) = case tactic of
  Intro _ _ -> []
  Assume _ -> []
  Suffices _ -> []
  ByContradiction _ -> []
  Subclaim t prf -> generateFromProof n p isContra hypo (termFromNF t) prf
  Choose vs t prf ->
    let ex = foldl' (\e (i, t) -> Exists i t e) t vs
    in generateFromProof n p isContra hypo ex prf
  Cases cs -> flip concatMap cs $ \(c, t, prf) -> 
    generateFromProof "case" p isContra (Given "case" c:hypo) t prf
  TerminalCases [] -> [] -- see use of foldl1 below
  TerminalCases cs ->
    let cases = flip concatMap cs $ \(c, prf) -> 
          generateFromProof "case" p isContra (Given "case" c:hypo) goal prf
        final = foldl1 (\a b -> App Or [a, b]) (map fst cs)
    in cases ++ [Task hypo final [] n isContra p]

-- runTactics :: Text -> SourcePos -> Bool -> Term Identity () -> [Hypothesis] -> [Located (Prf Identity ())] -> [Task]
runTactics :: Text -> SourcePos -> Bool -> Term Identity () -> [Hypothesis] -> [(Located (Prf Identity ()), Term Identity (), [Hypothesis])] -> [Task]
runTactics topName topPos isContra goal hypo [] = [Task hypo goal [] topName isContra topPos]
runTactics topName topPos isContra goal hypo ((tactic, newGoal, newHypos):ts) =
  let ts' = generateTask isContra goal hypo tactic
      isContra' = case tactic of
        Located _ _ (ByContradiction _) -> True
        _ -> isContra
  in ts' ++ runTactics topName topPos isContra' newGoal (newHypos ++ hypo) ts

-- | Generate tasks from the given proofs under the hypothesis that were assumed at this point.
generateFromProof :: Text -> SourcePos -> Bool -> [Hypothesis] -> Term Identity () -> PrfBlock Identity () -> [Task]
generateFromProof topname topPos isContra hypo topclaim (ProofByHints tophints)
  = [Task hypo topclaim tophints topname isContra topPos]
generateFromProof _ _ _ _ _ (ProofByTactics _)
  = Prelude.error "Internal error: Tactics to be generated were not type-checked!"
generateFromProof topname topPos isContra hypo topclaim (ProofByTCTactics prf)
  = runTactics topname topPos isContra topclaim hypo prf

generateTasks :: [Located (Stmt Identity ())] -> [Task]
generateTasks = concat . snd . mapAccumL go []
  where
    go hypo (Located n pos term) = case term of
      IntroSort t -> ((Typing t Sort):hypo, [])
      IntroAtom t _ ex _ -> ((Typing t (Pred (map (\(_, Identity b) -> b) ex) Prop)):hypo, [])
      IntroSignature t (Identity o) _ ex _ -> ((Typing t (Pred (map (\(_, Identity b) -> b) ex) (InType o))):hypo, [])
      Axiom t -> ((Given n (termFromNF t)):hypo, [])
      Predicate i (NFTerm im ex as b) ->
        let ts = map (\(_, Identity t) -> t) ex
            ax = termFromNF (NFTerm im ex as (App Iff [AppNF i [] (map (\(v, _) -> AppNF v [] [] []) ex) [], b]))
        in ((Given "" ax):(Typing i (Pred ts Prop)):hypo, [])
      Function i (Identity o) (NFTerm im ex as b) ->
        let ts = map (\(_, Identity t) -> t) ex
            ax = termFromNF (NFTerm im ex as (App Eq [AppNF i [] (map (\(v, _) -> AppNF v [] [] []) ex) [], b]))
        in ((Given "" ax):(Typing i (Pred ts (InType o))):hypo, [])
      Claim t prf -> ((Given n (termFromNF t)):hypo, generateFromProof n pos False hypo (termFromNF t) prf)
      Coercion n f t -> ((Typing n (Pred [Signature f] (InType (Signature t)))):hypo, [])