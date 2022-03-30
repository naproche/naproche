{-
Authors: Steffen Frerix (2017 - 2018), Makarius Wenzel (2022)

An implementation of the MESON algorithm.
-}

module SAD.Prove.MESON (Cache, init_cache, prune_cache, prove, contras, addRules)
where

import Control.Monad
import Control.Exception (evaluate)
import Data.List
import Data.Maybe
import qualified Data.Text.Lazy as Text

import SAD.Data.Formula
import SAD.Prove.Unify
import SAD.Prove.Normalize
import SAD.Data.Text.Context (Context, MRule(MR, conclusion))
import SAD.Helpers (notNull)
import qualified SAD.Data.Text.Context as Context
import SAD.Data.Structures.DisTree (DisTree)
import qualified SAD.Data.Structures.DisTree as DisTree
import qualified Isabelle.Cache as Cache
import qualified Isabelle.Time as Time
import Isabelle.Library (fold_rev)


-- generate MESON rules
contrapositives :: [Formula] -> [MRule]
contrapositives ls =
  let base = cps [] $ map ltNeg ls
  -- only generate a fact when all literals are negative
  in if all isNot ls then MR (map ltNeg ls) Bot : base else base
  where
    cps _ [] = []
    cps asms (l:ls) = MR (reverse asms ++ ls) (ltNeg l) : cps (l:asms) ls


{- the monadic action to generate meson rules during text verfication -}
contras :: Formula -> Int -> (([MRule], [MRule]), Int)
contras f m =
  let (skf, nm) = skolemize m $ simplify f
      cnf = transformToCNF skf
  in (splitContras $ concatMap contrapositives cnf, nm)

splitContras :: [MRule] -> ([MRule],[MRule])
splitContras = partition isPositive
  where
    isPositive = not . isNot . conclusion

addRules ::([MRule], [MRule])
  -> (DisTree MRule, DisTree MRule)
  -> (DisTree MRule, DisTree MRule)
addRules (pos, neg) (positives, negatives) =
  (fold_rev (DisTree.insertBy conclusion) pos positives,
   fold_rev (DisTree.insertBy (ltNeg . conclusion)) neg negatives)


-- MESON algorithm

{- implementation of the MESON algorithm.

   we check whether reasoning depth is exceeded,
   then whether we can close a branch because a literal is repeted.
   Otherwise we try to close the branch by unification or extend the branch
   with a MESON rule. -}
solve :: MonadPlus m => Int -> [MRule] -> DisTree MRule -> DisTree MRule
      -> [Formula] -> Formula -> m (Formula -> Formula)
solve n localRules positives negatives ancestors goal =
  guard (n >= 0) >> guard repCheck >> (closeBranch `mplus` expandBranch)
  where
    repCheck = all (isNothing . umatch goal) ancestors
    closeBranch = msum $ map closeWith ancestors
    expandBranch = msum $ map expandWith $ localRules ++
      if   isNot goal
      then DisTree.find (ltNeg goal) negatives
      else DisTree.find goal positives

    expandWith (MR assumptions conclusion) = do
      sbs <- unify conclusion goal
      --rename variables if necessary
      let renameSub = rename $ map sbs (goal:assumptions)
          (rnGoal:rnAssumptions) = map (renameSub . sbs) (goal:assumptions)
      sb <- solveGoals (n - length assumptions) (rnGoal:ancestors) rnAssumptions
      -- only pass down the relevant part of the substitution
      return $ relevantSbs goal (sb . renameSub . sbs)

    closeWith = unify (ltNeg goal)

    solveGoals _ _ [] = return id
    solveGoals m newAncestors (goal:goals) = do
      sbs <- solve m localRules positives negatives newAncestors goal
      fmap (sbs . ) $ solveGoals m newAncestors $ map sbs goals


{- find out which part of a substitution is actually relevant for the
current goal-}
relevantSbs :: Formula -> (Formula -> Formula) -> (Formula -> Formula)
relevantSbs f sb =
  let relevant = gatherUs [] $ ltAtomic f
  in  foldr (.) id $ map (\u -> subst (sb (mkVar u)) u) relevant
  where
    gatherUs ls Var {varName = x@(VarU _)} | x `notElem` ls = x : ls
    gatherUs ls t@Trm {trmArgs = tArgs} = foldl gatherUs ls tArgs
    gatherUs ls _ = ls

{- take care of variable names, rename if necessary. We employ two kinds of
  names, namely VarU names and VarHole names. This makes the whole bookkeeping
  process a bit easier. -}
rename :: [Formula] -> (Formula -> Formula)
rename fs = insertU
  where
    -- find the maximal 'u'-index and convert the '?'-names to 'u'
    insertU v@Var {varName = VarHole m} = v{varName = VarU $ Text.pack $ show(maxU + read (Text.unpack m) + 1)}
    insertU f = mapF insertU f

    maxU = myMaximum $ concatMap (foldF getU) fs
    getU Var {varName = VarU m} = [read $ Text.unpack m]; getU f = foldF getU f

    myMaximum :: [Int] -> Int
    myMaximum [] = -1
    myMaximum ls = maximum ls

{- checks whether the first formula is more general than the second in the
  context of MESON this is exactly the same as match, just with 'u':_
  instead of '?':_-}
umatch :: (MonadPlus m) => Formula -> Formula -> m (Formula -> Formula)
umatch Var {varName = v@(VarU _)} t = return  $ subst t v
umatch Var {varName = u} Var {varName = v} | u == v  = return id
umatch Trm {trmArgs = ps, trId = n} Trm {trmArgs = qs, trId = m}
  | n == m = pairs ps qs
  where
    pairs (p:ps) (q:qs) = do
      sb <- pairs ps qs
      sc <- umatch (sb p) q
      return $ sc . sb
    pairs [] []         = return id
    pairs _ _           = mzero
umatch _ _         = mzero



-- prove function

type Cache = Cache.T ([MRule], DisTree MRule, DisTree MRule) Bool

init_cache :: IO Cache
init_cache = Cache.init

prune_cache :: Cache -> IO ()
prune_cache cache = Cache.prune cache 10000 (Time.ms 1)

{- tries to prove a goal by employing MESON. First we split of the local
   premises that have not yet had their MESON rules computed and do so.
   Then we set a starting goal for MESON and see if MESON can solve the goal.
   The reasoning depth is fixed at the moment to 6 steps.

   n -> current counter for skolem constants; loc -> local context;
   ps -> positive global rules; ng -> negative global rules;
   gl -> goal.-}
prove :: Cache -> Int -> [Context] -> DisTree MRule -> DisTree MRule -> Formula -> IO Bool
prove cache n lowLevelContext positives negatives goal =
  let (localContext, proofContext) =
        span (null . Context.mesonRules) lowLevelContext
      localRules = makeContrapositives n $
        Not (deTag goal) : map (deTag . Context.formula) localContext
      startingRule = start (simplify $ Not goal)
      lowLevelRules =
        startingRule ++
        localRules   ++
        concatMap Context.mesonRules proofContext
  in
    Cache.apply cache (lowLevelRules, positives, negatives) $
      evaluate $ (notNull :: [a] -> Bool) $ solve 6 lowLevelRules positives negatives [] Bot
  where
    makeContrapositives _ [] = []
    makeContrapositives m (f:fs) =
      let (skf, nm) = skolemize m $ simplify f
      in  (concatMap contrapositives . transformToCNF) skf ++
          makeContrapositives nm fs
    
    start t@Trm{} = pure $ MR [ltNeg t] Bot
    start t@(Not Trm{}) = pure $ MR [ltNeg t] Bot
    start _ = []
