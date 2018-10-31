{-
Authors: Steffen Frerix (2017 - 2018)

Ontological reduction.
-}

module Alice.Core.Reduction where

import Alice.Data.Formula
import Alice.Data.Definition (DefEntry(DE))
import qualified Alice.Data.Definition as Definition
import Alice.Core.Base
import Alice.Prove.Normalize

import qualified Data.IntMap.Strict as IM
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List
import Data.Maybe
import Control.Monad.Trans.Class
import Control.Monad.State
import Control.Monad.Trans.Maybe

import Debug.Trace

{- ontoreduce and form universal closure-}
onto_reduce :: IM.IntMap DefEntry -> [Formula] -> Formula
onto_reduce _ [] = Top
onto_reduce dfs fs =
  let nds = filter (\g -> not $ elim 0 dfs g fs) fs
  in  case nds of
        [] -> Top
        [f] -> uClose [] f
        _   -> uClose [] $ foldr1 And (map ltNeg $ init nds) `Imp` last nds


{-tests eliminability-}
elim :: Int ->  IM.IntMap DefEntry -> Formula -> [Formula] -> Bool
elim n dfs f fs = not (null crits) && any (\g -> elim_f n dfs f g) crits && all (\g -> elim_f n dfs f g || elim_f n dfs g f) crits
  where
    crits = let fr_vr = free_st f in filter (\g -> not (ltTwins f g) && (not . null . Set.intersection fr_vr . free_st $ g)) fs
    -- crits are the formulas in fs that are critical for f

{-tests eliminability for a formula-}
elim_f :: Int -> IM.IntMap DefEntry -> Formula -> Formula -> Bool
elim_f n dfs f g = dive (free_st f) n g -- dive moves through the formula according to the calculus
  where
    dive vs n (And g h) = elim n dfs f [g,h]
    dive vs n (Or  g h) = elim n dfs f [g,h]
    dive vs n (Imp g h) = elim n dfs f [g,h]
    dive vs n (Not g) = dive vs n g
    dive vs n (All _ g) = dive vs (succ n) $ inst (show n) g
    dive vs n (Exi _ g) = dive vs (succ n) $ inst (show n) g
    dive vs n (Iff g h) = elim n dfs f [g,h]
    dive vs n (Tag _ g) = dive vs n g
    dive vs n t@Trm {trId = m, trArgs = ts}
      = let ft = free_st t in
         if Set.null $ Set.intersection vs ft then False -- False if f and t share no variables
                                              else dive_t vs t -- else check if f is eliminable for t


    dive_t _ v@Var{} = True
    dive_t _ Trm {trName = 't':'s':'k':_} = False -- nothing is eliminable for a skolem constant
    dive_t vs t@Trm {trId = m, trArgs = ts} =
      (if not . Set.null $ Set.intersection vs $ free_Top t then
      let df = fromJust $ IM.lookup m dfs; sb = fromJust $ match (Definition.term df) t
       in atom_elim sb (invImage sb (Definition.term df) vs) (Definition.typeLikes df) f vs
      else True) && allF (dive_t vs) t

{-form the inverse image of the variables of f under the substitution sb -}
invImage :: (Formula -> Formula) -> Formula -> Set.Set String -> Set.Set String
invImage sb f ft = Set.fromList [ x | x <- allFree [] f, trName (sb (zVar x)) `Set.member` ft]

{-tests eliminability for an atomic formula-}
atom_elim :: (Formula -> Formula) -> Set.Set String -> [[Formula]] -> Formula -> Set.Set String -> Bool
atom_elim sb inv tp f vs = case find (any (reveal_rn sb (albet $ Not f))) tp of --find suitable domain conditions of the atom
  Nothing -> False -- if nothing is suitable then the formula is not eliminable
  Just dc -> (all (covered dc) inv) &&  all (reveal (albet $ Not f)) (map sb $ covering inv dc) -- otherwise check the covering condition
  where
    covered dc v = let dc_vars = map free_st dc in any (Set.member v) dc_vars
    covering inv = filter $ any (`Set.member` inv) . free_st

{-tests if a domain condition of a symbol is type like-}
type_like :: IM.IntMap DefEntry -> Formula -> [Formula] -> Bool
type_like dfs f = all (\g -> if Set.null $ Set.intersection (free_st f) (free_st g) then True else twins f g || elim_f 0 dfs (Not f) g || elim_f 0 dfs (Not g) f)

{-we abstract over the heuristic used to reveal equivalence  of formulas-}
reveal = twins -- since we only concern ourselves with literals, we use syntactic equality

data RvState = RV {frsh :: Int, assgn :: Map.Map String String, alrdyassgn :: Set.Set String}

{- checks whether sb is a renaming from g to f and if sb g is syntactically equal to f after alpha-beta normalization -}
reveal_rn sb f g = isJust $ fst $ runState (runMaybeT $ rv_al f g) $ RV 0 Map.empty Set.empty
  where
    rv_al f g = rv (albet f) (albet g)
    rv (And f1 g1) (And f2 g2) = rv_al f1 f2 >> rv_al g1 g2;
    rv (Or  f1 g1) (Or  f2 g2) = rv_al f1 f2 >> rv_al g1 g2
    rv (All _ f)   (All _ g)   = do v <- freshV; rv_al (inst v f) (inst v g)
    rv (Exi _ f)   (Exi _ g)   = do v <- freshV; rv_al (inst v f) (inst v g)

    rv Trm {trId = tId1, trArgs = ts1} Trm {trId = tId2, trArgs = ts2}
      | tId1 == tId2 = mapM_ (\(f,g) -> rv f g) $ zip ts1 ts2
    rv Var{trName = v} vr@Var {trName = u@('?':_)} | isVar $ sb vr
      = do mp <- lift $ gets assgn; al <- lift $ gets alrdyassgn
           case (Map.lookup u mp, Set.member v al) of
             (Just x, True) -> guard (x == v)
             (Nothing, False) -> let nu = trName $ sb vr in
                                  lift $ modify (\st -> st {assgn = Map.insert u nu mp, alrdyassgn = Set.insert nu al }) >> return ()
             _ -> mzero
    rv Var{trName = u} Var {trName = v} = guard (u == v)

    rv _ _ = mzero

    freshV = do n <- lift $ gets frsh; lift $ modify (\st -> st {frsh = n + 1}); return $ show n

{-collects the variables that occur freely on the top level of the term-}
free_Top = Set.unions .map free_tp . trArgs
  where
    free_tp Var{trName = x} = Set.singleton x
    free_tp _ = Set.empty

{-collects the free variables of a formula and puts them in a set-}
free_st :: Formula -> Set.Set String
free_st Var{trName = x} = Set.singleton x
free_st f = foldF free_st f
