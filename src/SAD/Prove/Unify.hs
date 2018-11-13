{-
Authors: Steffen Frerix (2017 - 2018)

Unification of literals.
-}



module SAD.Prove.Unify (unify) where

import Control.Monad
import Control.Monad.Trans.Writer

import SAD.Data.Formula


import Debug.Trace


{- given two literals we check whether they are eligible for unification
(sign and symbol are the same) and then try to unify their arguments-}
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
unify l r = guard (ltId l == ltId r) >> unif (zip (ltArgs l) (ltArgs r))

{- implementation of a standard unification algorithm -}
unif :: MonadPlus m => [(Formula, Formula)] -> m (Formula -> Formula)
unif = fmap mkSubst . dive [] -- we keep a list of already assigned variables
  where
    dive assigned (task@(l,r):rest)
      | functionSymb l && functionSymb r -- if both sides have a function symbol
          = if clash l r then mzero else dive assigned (newTasks l r ++ rest)
      | functionSymb l = dive assigned $ (r, l) : rest
      | otherwise
          = if occurs l r then mzero  -- occurs check
          -- save the assignment and unify the rest under this assignment
            else dive (task:assigned) $ map (ufSub l r) rest
    dive assigned _ = return assigned

    --------------------- auxiliary functions
    ufSub x t (l,r) = let sb = subst t (trName x) in (sb l, sb r)

    newTasks Trm {trArgs = tArgs} Trm {trArgs = sArgs} = zip tArgs sArgs
    newTasks _ _ = []

    -- update earlier assignments with later ones
    mkSubst ((x,t):rst) =
      let sb = subst t (trName x)
      in  sb . mkSubst (map (\(x',t') -> (x', sb t')) rst)
    mkSubst [] = id



    clash Trm {trId = tId} Trm {trId = sId} = tId /= sId
    clash Var {trName = x} Var {trName = y} = x /= y
    clash _ _ = True

    -- all other vars are treated as constants
    functionSymb Var {trName = '?':_} = False
    functionSymb Var {trName = 'u':_} = False
    functionSymb _ = True
