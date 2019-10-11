{-
Authors: Steffen Frerix (2017 - 2018)

Normalization of formulas.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module SAD.Prove.Normalize  (
  simplify,
  dec, inc,
  skolemize,
  transformToCNF,
  assm_nf, impl, ontoPrep,
  isSkolem
  ) where

import SAD.Data.Formula
import SAD.Data.TermId
import SAD.Core.SourcePos

import Data.List
import qualified Data.Text.Lazy as Text
import qualified SAD.Data.Text.Decl as Decl
import SAD.Data.VarName



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
pushdown (All _ (Imp (Tag HeadTerm Trm {trmName = "=", trmArgs = [_,t]} ) f)) =
  pushdown $ dec $ indSubst t VarEmpty $ inst VarEmpty f
pushdown (All _ (Iff (Tag HeadTerm eq@Trm {trmName = "=", trmArgs = [_,t]}) f)) =
  And (All (Decl.nonText VarEmpty) (Or eq (Not f))) $ dec $ indSubst t VarEmpty $ inst VarEmpty f
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
    increment n v@Ind {indIndex = i} = v {indIndex = if n <= i then succ i else i}
    increment n (All x f)  = All x $ increment (succ n) f
    increment n (Exi x f)  = Exi x $ increment (succ n) f
    increment n f = mapF (increment n) f

{- decrease de Bruijn indices -}
dec :: Formula -> Formula
dec = decrement 0
  where
    decrement n v@Ind {indIndex = i} = v {indIndex = if n <= i then pred i else i}
    decrement n (All x f)  = All x $ decrement (succ n) f
    decrement n (Exi x f)  = Exi x $ decrement (succ n) f
    decrement n f = mapF (decrement n) f


indSubst :: Formula -> VariableName -> Formula -> Formula
indSubst t v = dive t
  where
    dive t (All x f) = All x $ dive (inc t) f
    dive t (Exi x f) = Exi x $ dive (inc t) f
    dive t Var {varName = u} | u == v = t
    dive t f = mapF (dive t) f

-- | Skolemization
skolemize :: Int -> Formula -> (Formula, Int)
skolemize n f = let (sc, _, fs) = dive (n, 0, id) f in (fs, sc)
  where
    -- sc: skolemCounter, dc: dependencyCounter, fs: Formula visited so far
    dive (sc, dc, fs) (All x f) = dive (sc, succ dc, fs . All x) f
    dive (sc, dc, fs) (Exi _ f) = dive (succ sc, dc, fs) (dec $ instSk sc dc f)
    dive (sc, dc, fs) (Or  f g) = 
      let (sc', _, fs') = dive (sc, dc, id) f in dive (sc', dc, fs . Or  fs') g
    dive (sc, dc, fs) (And f g) =
      let (sc', _, fs') = dive (sc, dc, id) f in dive (sc', dc, fs . And fs') g
    dive (sc, dc, fs) f = (sc, dc, fs f)

instSk :: Int -> Int -> Formula -> Formula
instSk skolemCnt dependencyCnt = dive 0
  where
    dive d (All x f) = All x $ dive (succ d) f
    dive d (Exi x f) = Exi x $ dive (succ d) f
    dive d Ind {indIndex = m} | d == m = skolemFunction d
    dive d f = mapF (dive d) f

    skolemFunction = zTrm (SkolemId skolemId) skolemName . skolemArguments


    skolemArguments d = [Ind (i + d) noSourcePos | i <- [1..dependencyCnt] ]

    skolemId = -20 - skolemCnt
    skolemName = Text.pack $ "tsk" ++ show skolemCnt



-- specialization of formula: get rid of universal quantifiers

specialize :: Formula -> Formula
specialize = specCh (VarHole . Text.pack . show) 0

specCh :: (Int -> VariableName) -> Int -> Formula -> Formula
specCh mkVar = dive
  where
    dive n (All _ f) = dive (succ n) $ inst (mkVar n) f
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


{-| Does every formula from the first list have an 'ltTwins' in the second? -}
listEq :: [Formula] -> [Formula] -> Bool
listEq [] [] = True
listEq (l:ls) rs = case helper [] l rs of
                          Nothing -> False
                          Just nrs -> listEq ls nrs
  where
    helper _ _ [] = Nothing
    helper dmp l (r:rs) = if ltTwins l r then return $ dmp ++ rs
                          else helper (r:dmp) l rs

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
assm_nf = map (imptolist . boolSimp . specCh VarAssume 0) . splitConjuncts . impl
  where
    imptolist (Imp f g) = map ltNeg (splitConjuncts f) ++ imptolist g
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
      specializedF = specCh VarSkolem 0 . prenex $ nf
      conjuncts = leftDistribute specializedF
  in  (conjuncts, nsk)
  where
    leftDistribute (Or f g) = map (Or f) $ leftDistribute g
    leftDistribute (And f g) = leftDistribute f ++ leftDistribute g
    leftDistribute f = [f]


-- testing for skolem function

isSkolem :: Formula -> Bool
isSkolem Trm {trmId = SkolemId _} = True
isSkolem _ = False
