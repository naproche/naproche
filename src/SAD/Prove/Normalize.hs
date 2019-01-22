{-
Authors: Steffen Frerix (2017 - 2018)

Normalization of formulas.
-}


{-# LANGUAGE FlexibleContexts #-}

module SAD.Prove.Normalize  (
  simplify,
  dec, inc,
  skolemize,
  transformToCNF,
  assm_nf, impl, ontoPrep,
  isSkolem
  ) where

import SAD.Data.Formula


import Data.List
import Control.Monad.State
import Debug.Trace
import qualified SAD.Data.Text.Decl as Decl



-- simplification : push down negation, replace implication and equivalence

simplify :: Formula -> Formula
simplify f = mapF simplify . nbool . pushdown $ f
  where
    nbool (Or Top _) = Top
    nbool (Or _ Top) = Top
    nbool (Or f Bot) = f
    nbool (Or Bot f) = f
    nbool (And Bot _) = Bot
    nbool (And _ Bot) = Bot
    nbool (And f Top) = f
    nbool (And Top f) = f
    nbool (Not Top) = Bot
    nbool (Not Bot) = Top
    nbool (Tag _ f) = nbool f
    nbool f = f


pushdown :: Formula -> Formula
pushdown (Iff f g)       = And (Or (Not f) g) (Or f (Not g))
pushdown (Imp f g)       = Or (Not f) g
pushdown (Not (All x f)) = Exi x $ Not f
pushdown (Not (Exi x f)) = All x $ Not f
pushdown (Not (Iff f g)) = And (Or f g) (Or (Not f) (Not g))
pushdown (Not (Imp f g)) = And f (Not g)
pushdown (Not (And f g)) = Or (Not f) (Not g)
pushdown (Not (Or  f g)) = And (Not f) (Not g)
pushdown (Not (Not f))   = pushdown f
pushdown (Not Bot)       = Top
pushdown (Not Top)       = Bot
pushdown (Tag _ f) = pushdown f
pushdown (Not (Tag _ f)) = pushdown (Not f)
pushdown (All _ (Imp (Tag HeadTerm Trm {trName = "=", trArgs = [_,t]} ) f)) =
  pushdown $ dec $ indSubst t "" $ inst "" f
pushdown (All _ (Iff (Tag HeadTerm eq@Trm {trName = "=", trArgs = [_,t]}) f)) =
  And (All (Decl.nonText "") (Or eq (Not f))) $ dec $ indSubst t "" $ inst "" f
pushdown f = f


-- prenex normal form

pullquants :: Formula -> Formula
pullquants (And (All x f) (All y g)) = All x (pullquants $ And f g)
pullquants (Or  (Exi x f) (Exi y g)) = Exi x (pullquants $ Or  f g)
pullquants (And (All x f) g) = All x (pullquants $ And f $ inc g)
pullquants (And f (All y g)) = All y (pullquants $ And (inc f) g)
pullquants (Or  (All x f) g) = All x (pullquants $ Or  f $ inc g)
pullquants (Or  f (All y g)) = All y (pullquants $ Or  (inc f) g)
pullquants (And (Exi x f) g) = Exi x (pullquants $ And f $ inc g)
pullquants (And f (Exi y g)) = Exi y (pullquants $ And (inc f) g)
pullquants (Or  (Exi x f) g) = Exi x (pullquants $ Or  f $ inc g)
pullquants (Or  f (Exi y g)) = Exi y (pullquants $ Or  (inc f) g)
pullquants f = f

prenex :: Formula -> Formula
prenex (All x f) = All x $ prenex f
prenex (Exi x f) = Exi x $ prenex f
prenex (And f g) = pullquants $ And (prenex f) (prenex g)
prenex (Or  f g) = pullquants $ Or  (prenex f) (prenex g)
prenex f = f


-- Index manangement

{- increase all de Bruijn indices -}
inc :: Formula -> Formula
inc = increment 0
  where
    increment n v@Ind {trIndx = i} = v {trIndx = if n <= i then succ i else i}
    increment n (All x f)  = All x $ increment (succ n) f
    increment n (Exi x f)  = Exi x $ increment (succ n) f
    increment n f = mapF (increment n) f

{- decrease de Bruijn indices -}
dec :: Formula -> Formula
dec = decrement 0
  where
    decrement n v@Ind {trIndx = i} = v {trIndx = if n <= i then pred i else i}
    decrement n (All x f)  = All x $ decrement (succ n) f
    decrement n (Exi x f)  = Exi x $ decrement (succ n) f
    decrement n f = mapF (decrement n) f


indSubst :: Formula -> String -> Formula -> Formula
indSubst t v = dive t
  where
    dive t (All x f) = All x $ dive (inc t) f
    dive t (Exi x f) = Exi x $ dive (inc t) f
    dive t Var {trName = u} | u == v = t
    dive t f = mapF (dive t) f

-- skolemization


data SkState = SK { skolemCounter :: Int, dependencyCounter :: Int}

skolemize :: Int -> Formula -> (Formula, Int)
skolemize n f =
  let (skf, SK {skolemCounter = nsk}) = runState (skolem f) $ SK n 0
  in  (skf, nsk)
  where
    skolem (All x f) = fmap (All x) $ increaseDependency >> skolem f
    skolem (Exi _ f) = instSkolem f >>= skolem . dec
    skolem (Or  f g) = do
      st <- get; liftM2 Or  (skolem f) (resetDependency st >> skolem g)
    skolem (And f g) = do
      st <- get; liftM2 And (skolem f) (resetDependency st >> skolem g)
    skolem f = return f

    increaseDependency =
      modify (\st -> st {dependencyCounter = succ (dependencyCounter st)})
    resetDependency st =
      modify (\ost -> ost { dependencyCounter = dependencyCounter st})

instSkolem :: Formula -> State SkState Formula
instSkolem f = do
  st <- get; let nf = instSk (skolemCounter st) (dependencyCounter st) f
  put $ st { skolemCounter = succ (skolemCounter st) }; return nf

instSk :: Int -> Int -> Formula -> Formula
instSk skolemCnt dependencyCnt = dive 0
  where
    dive d (All x f) = All x $ dive (succ d) f
    dive d (Exi x f) = Exi x $ dive (succ d) f
    dive d Ind {trIndx = m} | d == m = skolemFunction d
    dive d f = mapF (dive d) f

    skolemFunction = zTrm skolemId skolemName . skolemArguments


    skolemArguments d = [Ind (i + d) undefined | i <- [1..dependencyCnt] ]

    skolemId = -20 - skolemCnt
    skolemName = "tsk" ++ show skolemCnt



-- specialization of formula: get rid of universal quantifiers

specialize :: Formula -> Formula
specialize = specCh '?' 0

specCh :: Char -> Int -> Formula -> Formula
specCh c = dive
  where
    dive n (All _ f) = dive (succ n) $ inst (c:show n) f
    dive n f = f


-- Conversion to CNF

transformToCNF :: Formula -> [[Formula]]
transformToCNF = simpCNF . specialize . prenex

simpCNF :: Formula -> [[Formula]]
simpCNF Top = [[]]
simpCNF Bot = []
simpCNF f = subsumptionCheck $ filter (not . trivial) $ pureCNF f

pureCNF :: Formula -> [[Formula]]
pureCNF (And f g) = unionBy listEq (pureCNF f) (pureCNF g)
pureCNF (Or f g)  = distrib (pureCNF f) (pureCNF g)
pureCNF f = [[f]]


distrib :: [[Formula]] -> [[Formula]] -> [[Formula]]
distrib ls rs = nubBy listEq $ allpairs (unionBy ltTwins) ls rs


listEq :: [Formula] -> [Formula] -> Bool
listEq [] [] = True
listEq (l:ls) rs = case helper [] l rs of
                          Nothing -> False
                          Just nrs -> listEq ls nrs
  where
    helper _ _ [] = Nothing
    helper dmp l (r:rs) = if ltTwins l r then return $ dmp ++ rs
                          else helper (r:dmp) l rs
listEq _ _ = False

trivial :: [Formula] -> Bool
trivial [] = False
trivial (l:ls) = isTop l || any (ltTwins $ ltNeg l) ls || trivial ls

allpairs :: (a -> b -> c) -> [a] -> [b] -> [c]
allpairs f [] _ = []
allpairs f (a:as) bs = map (f a) bs ++ allpairs f as bs


subsumptionCheck :: [[Formula]] -> [[Formula]]
subsumptionCheck = subs []
  where
    subs _ [] = []
    subs dmp (ls:lss) | any (subsumes ls) (dmp ++ lss) = subs dmp lss
                      | otherwise = ls : subs (ls:dmp) lss

    subsumes _ [] = True
    subsumes ls (r:rs) | any (ltTwins r) ls = subsumes ls rs
                       | otherwise = False


-- assumption normal form

assm_nf :: Formula -> [[Formula]]
assm_nf = map (imptolist . boolSimp . specCh 'i' 0) . deAnd . impl
  where
    imptolist (Imp f g) = map ltNeg (deAnd f) ++ imptolist g
    imptolist f = [f]


impl :: Formula -> Formula
impl (All x (Imp f g)) = All x $ pullimp $ Imp f $ impl g
impl (All x f)         = All x $ impl f
impl (Imp f (And g h)) = impl $ And (Imp f g) (Imp f h)
impl (Imp f g)         = pullimp $ Imp f $ impl g
impl (And f g)         = And (impl f) (impl g)
impl f = f

pullimp :: Formula -> Formula
pullimp (Imp f (All x g)) = All x $ pullimp $ Imp (inc f) g
pullimp (Imp f (Imp g h)) = pullimp $ Imp (And f g) h
pullimp f = f

ontoPrep :: Int -> Formula -> ([Formula], Int)
ontoPrep sk f =
  let (nf, nsk) = skolemize sk $ simplify f
      specializedF = specCh 'o' 0 . prenex $ nf
      conjuncts = leftDistribute specializedF
  in  (conjuncts, nsk)
  where
    leftDistribute (Or f g) = map (Or f) $ leftDistribute g
    leftDistribute (And f g) = leftDistribute f ++ leftDistribute g
    leftDistribute f = [f]


-- testing for skolem function

isSkolem :: Formula -> Bool
isSkolem Trm {trName = 't':'s':'k':_} = True
isSkolem _ = False
