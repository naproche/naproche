{-
Authors: Steffen Frerix (2017 - 2018)

An implementation of the MESON algorithm.
-}


module Alice.Prove.MESON (prove, contras) where

import Control.Monad

import Alice.Core.Base hiding (retrieve)
import Alice.Data.Formula
import Alice.Prove.Unify
import Alice.Prove.Normalize
import Alice.Data.Text.Context (Context, MRule(MR))
import qualified Alice.Data.Text.Context as Context
import qualified Alice.Data.Structures.DisTree as DT
import Alice.Core.Reduction

import Debug.Trace
import Data.Maybe

-- generate MESON rules
contrapositives :: [Formula] -> [MRule]
contrapositives ls = let base = cps [] $ map ltNeg ls
                      in if all isNot ls then MR (map ltNeg ls) Bot : base else base -- we only generate a fact if all literals are negative
  where
    cps _ [] = []
    cps asms (l:ls) = MR (reverse asms ++ ls) (ltNeg l) : cps (l:asms) ls


{- the monadic action to generate meson rules during text verfication -}
contras b f = do m <- askGlobalState skolemCounter;
                 let (skf, SK { sk = nm }) = sklm m $ simplify f
                 updateGlobalState (\st -> st { skolemCounter = nm })
                 let cnf = simpcnf . spec 0 . prenex  $ skf
                 return $ concatMap contrapositives cnf


-- MESON algorithm

{- implementation of the MESON algorithm. As a result we obtain a substitution that
   provides witnesses for the existentially quantified variables.

   n -> reasoning depth; loc -> local context; ps -> positive literals; ng -> negative literals;
   anc -> ancestors, g -> goal.

   we check whether reasoning depth is exceeded, then whether we can close a branch because a literal is repeted.
   Otherwise we try to close the branch by unification or extend the branch with a MESON rule. -}
solve :: MonadPlus m => Int -> [MRule] -> DT.DisTree MRule -> DT.DisTree MRule
      -> [Formula] -> Formula -> m (Formula -> Formula)
solve n loc ps ng anc g = guard (n >= 0) >> guard repCheck >> (closeBranch `mplus` expandBranch)
  where
    repCheck = all (isNothing . umatch g) anc
    closeBranch = msum $ map closeWith anc
    expandBranch = msum $ map expandWith $ (loc ++ if isNot g then DT.find (ltNeg g) ng else DT.find g ps)

    expandWith (MR assumption c) = do
      sbs <- unify c g
      let rnsb = rename $ map sbs (g:assumption) --rename vars if necessary
          (ng:nasm) = map (rnsb . sbs) (g:assumption)
      sb <- solveGls (n - length assumption) (ng : anc) nasm -- solve remaining goals
      return $ relevantSbs g (sb . rnsb . sbs)
      -- only pass down the relevant part of the substitution
    closeWith p = unify (ltNeg g) p

    solveGls _ _ [] = return id
    solveGls m nAnc (g:gls) = do sbs <- solve m loc ps ng nAnc g
                                 liftM ((.) sbs) $ solveGls m nAnc $ map sbs gls


{- find out which part of a substitution is actually relevant for the current goal-}
relevantSbs :: Formula -> (Formula -> Formula) -> (Formula -> Formula)
relevantSbs f sb = let rlvnt = gatherUs [] $ ltAtomic f
                    in foldr (.) id $ map (\u -> subst (sb (zVar u)) u) rlvnt
  where
    gatherUs ls Var {trName = s@('u':_)} | not $ elem s ls = s : ls
    gatherUs ls t@Trm {trArgs = ts} = args ls ts
    gatherUs ls f = ls

    args ls [] = ls
    args ls (t:ts) = let nls = gatherUs ls t in args nls ts

{- take care of variable names, rename if necessary. We employ to kinds of names,
   namely 'u':_ names and '?':_ names. This makes the whole bookkeeping process
   a bit easier. -}
rename :: [Formula] -> (Formula -> Formula)
rename fs = insertU
  where
    insertU v@Var {trName = '?':m} = v{trName = 'u':show(maxU + read m + 1)} -- find the maximal 'u'-index and convert the '?'-names to 'u'
    insertU f = mapF insertU f

    maxU = myMaximum $ map maxU' fs
    maxU' f = myMaximum $ foldF getU f

    getU Var {trName = 'u':m} = [read m]
    getU f = foldF getU f

    myMaximum [] = -1
    myMaximum ls = maximum ls

{-iterative deepening -}
deepen f n = f n `mplus` (deepen f (n + 1))

{- checks whether the first formula is more general than the second in the context of MESON
   this is exactly the same as match, just with 'u':_ instead of '?':_-}
umatch :: (MonadPlus m) => Formula -> Formula -> m (Formula -> Formula)
umatch Var {trName = v@('u':_)} t       = return  $ subst t v
umatch Var {trName  = u} Var {trName = v}    | u == v  = return id
umatch Trm {trArgs = ps, trId = n} Trm {trArgs = qs, trId = m}| n == m  = pairs ps qs
  where
    pairs (p:ps) (q:qs) = do  sb <- pairs ps qs
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
prove :: Int -> [Context] -> DT.DisTree MRule -> DT.DisTree MRule -> Context -> Bool
prove n loc ps ng gl = let (vlc, mlc) = span (null . Context.mesonRules) loc
                           nrl = cs n $ (Not $ deTag $ Context.formula gl) : map (deTag . Context.formula) vlc
                           rls = start (simplify $ Not $ Context.formula gl) ++ nrl ++ concatMap Context.mesonRules mlc
                           in not . (null :: [a] -> Bool) $ solve 6 rls ps ng [] Bot
  where
    cs _ [] = []
    cs m (f:fs) = let (skf, SK { sk = nm }) = sklm m $ simplify f
                   in (concatMap contrapositives . simpcnf . spec 0 . prenex) skf ++ cs nm fs
    start t | isLiteral t || isEquality t = pure $ MR [ltNeg t] Bot
            | otherwise = []
