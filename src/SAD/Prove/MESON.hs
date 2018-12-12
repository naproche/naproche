{-
Authors: Steffen Frerix (2017 - 2018)

An implementation of the MESON algorithm.
-}


module SAD.Prove.MESON (prove, contras, addRules) where

import Control.Monad
import Control.Monad.Reader
import Data.List

import SAD.Core.Base hiding (retrieve)
import SAD.Data.Formula
import SAD.Prove.Unify
import SAD.Prove.Normalize
import SAD.Data.Text.Context (Context, MRule(MR, conclusion))
import qualified SAD.Data.Text.Context as Context
import qualified SAD.Data.Structures.DisTree as DT
import SAD.Core.Reduction

import Debug.Trace
import Data.Maybe

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
contras :: Formula -> VM (([MRule], [MRule]), Int)
contras f = do
  m <- asks skolemCounter;
  let (skf, nm) = skolemize m $ simplify f
      cnf = transformToCNF skf
  return (splitContras $ concatMap contrapositives cnf, nm)

splitContras :: [MRule] -> ([MRule],[MRule])
splitContras = partition isPositive
  where
    isPositive = not . isNot . conclusion

addRules ::
  (DT.DisTree MRule, DT.DisTree MRule) ->
  ([MRule], [MRule]) ->
  (DT.DisTree MRule, DT.DisTree MRule)
addRules (pos, neg) (newPos, newNeg) =
  (foldr (DT.insertBy conclusion) pos newPos,
  foldr (DT.insertBy (ltNeg. conclusion)) neg newNeg)


-- MESON algorithm

{- implementation of the MESON algorithm.

   we check whether reasoning depth is exceeded,
   then whether we can close a branch because a literal is repeted.
   Otherwise we try to close the branch by unification or extend the branch
   with a MESON rule. -}
solve :: MonadPlus m => Int -> [MRule] -> DT.DisTree MRule -> DT.DisTree MRule
      -> [Formula] -> Formula -> m (Formula -> Formula)
solve n localRules positives negatives ancestors goal =
  guard (n >= 0) >> guard repCheck >> (closeBranch `mplus` expandBranch)
  where
    repCheck = all (isNothing . umatch goal) ancestors
    closeBranch = msum $ map closeWith ancestors
    expandBranch = msum $ map expandWith $ localRules ++
      if   isNot goal
      then DT.find (ltNeg goal) negatives
      else DT.find goal positives

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
  in  foldr (.) id $ map (\u -> subst (sb (zVar u)) u) relevant
  where
    gatherUs ls Var {trName = x@('u':_)} | x `notElem` ls = x : ls
    gatherUs ls t@Trm {trArgs = tArgs} = foldl gatherUs ls tArgs
    gatherUs ls _ = ls

{- take care of variable names, rename if necessary. We employ two kinds of
  names, namely 'u':_ names and '?':_ names. This makes the whole bookkeeping
  process a bit easier. -}
rename :: [Formula] -> (Formula -> Formula)
rename fs = insertU
  where
    -- find the maximal 'u'-index and convert the '?'-names to 'u'
    insertU v@Var {trName = '?':m} = v{trName = 'u':show(maxU + read m + 1)}
    insertU f = mapF insertU f

    maxU = myMaximum $ concatMap (foldF getU) fs
    getU Var {trName = 'u':m} = [read m]; getU f = foldF getU f

    myMaximum [] = -1
    myMaximum ls = maximum ls

{-iterative deepening -}
deepen f n = f n `mplus` deepen f (n + 1)

{- checks whether the first formula is more general than the second in the
  context of MESON this is exactly the same as match, just with 'u':_
  instead of '?':_-}
umatch :: (MonadPlus m) => Formula -> Formula -> m (Formula -> Formula)
umatch Var {trName = v@('u':_)} t = return  $ subst t v
umatch Var {trName = u} Var {trName = v} | u == v  = return id
umatch Trm {trArgs = ps, trId = n} Trm {trArgs = qs, trId = m}
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

{- tries to prove a goal by employing MESON. First we split of the local
   premises that have not yet had their MESON rules computed and do so.
   Then we set a starting goal for MESON and see if MESON can solve the goal.
   The reasoning depth is fixed at the moment to 6 steps.

   n -> current counter for skolem constants; loc -> local context;
   ps -> positive global rules; ng -> negative global rules;
   gl -> goal.-}
prove :: Int -> [Context] -> DT.DisTree MRule -> DT.DisTree MRule -> Context
      -> Bool
prove n lowLevelContext positives negatives goal =
  let (localContext, proofContext) =
        span (null . Context.mesonRules) lowLevelContext
      localRules = makeContrapositives n $
        (Not $ deTag $ Context.formula goal) :
        map (deTag . Context.formula) localContext
      startingRule = start (simplify $ Not $ Context.formula goal)
      lowLevelRules =
        startingRule ++
        localRules   ++
        concatMap Context.mesonRules proofContext
  in  not . (null :: [a] -> Bool) $
      solve 6 lowLevelRules positives negatives [] Bot
  where
    makeContrapositives _ [] = []
    makeContrapositives m (f:fs) =
      let (skf, nm) = skolemize m $ simplify f
      in  (concatMap contrapositives . transformToCNF) skf ++
          makeContrapositives nm fs
    start t
      | isLiteral t || isEquality t = pure $ MR [ltNeg t] Bot
      | otherwise = []
