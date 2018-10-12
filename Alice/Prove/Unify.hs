{-
Authors: Steffen Frerix (2017 - 2018)

Unification of literals.
-}



module Alice.Prove.Unify (unify) where

import Control.Monad
import Control.Monad.Trans.Writer

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit


import Debug.Trace


{- given two literals we check whether they are eligible for unification (sign and symbol
   are the same) and then try to unify their arguments-}
unify :: MonadPlus m => Formula -> Formula -> m (Formula -> Formula)
unify (Not l) (Not r) = unify l r
unify l (Not r) = mzero
unify (Not l) r = mzero
unify Bot Bot = return id
unify Bot _ = mzero
unify _ Bot = mzero
unify Top Top = return id
unify Top _ = mzero
unify _ Top = mzero
unify l r = do guard $ ltId l == ltId r
               unif $ zip (ltArgs l) (ltArgs r)

{- implementation of a standard unification algorithm -}
unif :: MonadPlus m => [(Formula, Formula)] -> m (Formula -> Formula)
unif = liftM mkSubst . dive [] -- we keep a list of already assigned variables that is empty at the start
  where
    dive as (tsk@(l,r):rst) -- while there still is a unification task
      | (not . isfVar) l && (not . isfVar) r -- if both sides have a function symbol
          = if clash l r then mzero else dive as (newTsks l r ++ rst) -- check for clash, else unify arguments
      | (not . isfVar) l = dive as $ (r, l) : rst -- if only the right side is a variable, switch sides
      | otherwise -- if the left side is a variable
          = if occurs l r then mzero  -- occurs check
            else dive (tsk:as) $ map (ufSub l r) rst -- save the assignment and unify the rest under this assignment
    dive as [] = return as -- if all the tasks are completed, return the assignments

    --------------------- auxiliary functions
    ufSub x t (l,r) = let sb = subst t (trName x) in (sb l, sb r)

    newTsks Trm {trArgs = ts} Trm {trArgs = ss} = zip ts ss
    newTsks _ _ = []

    mkSubst ((x,t):rst) -- to turn the recorded assignments into a substitution we must update earlier assingments with the later ones
      = let sb = subst t (trName x)
         in sb . mkSubst (map (\(x',t') -> (x', sb t')) rst)
    mkSubst [] = id



    clash Trm {trId = tId} Trm {trId = sId} = not $ tId == sId
    clash Var {trName = x} Var {trName = y} = not $ x == y
    clash _ _ = True

    isfVar Var {trName = '?':_} = True -- only these two are considered free variables
    isfVar Var {trName = 'u':_} = True -- all other Vars are treated as constants
    isfVar _ = False
