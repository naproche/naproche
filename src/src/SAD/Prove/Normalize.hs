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

import Data.List
import qualified Data.Text.Lazy as Text
import SAD.Data.Text.Decl

import qualified Isabelle.Position as Position


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
pushdown (All _ (Imp (Tag HeadTerm Trm {trmName = TermEquality, trmArgs = [_,t]} ) f)) =
  pushdown $ dec $ indSubst t VarEmpty $ inst VarEmpty f
pushdown (All _ (Iff (Tag HeadTerm eq@Trm {trmName = TermEquality, trmArgs = [_,t]}) f)) =
  And (All (newDecl VarEmpty) (Or eq (Not f))) $ dec $ indSubst t VarEmpty $ inst VarEmpty f
pushdown f = f


-- | Prenex normal form of a formula.
prenex :: Formula -> Formula
prenex = \case
  All x f -> All x (prenex f)
  Exi x f -> Exi x (prenex f)
  f `And` g -> pullQuantifiers (prenex f `And` prenex g)
  f `Or` g  -> pullQuantifiers (prenex f `Or`  prenex g)
  f -> f
  where
    pullQuantifiers :: Formula -> Formula
    pullQuantifiers = \case
      All x f `And` All y g -> All x (pullQuantifiers (f     `And` g))
      Exi x f `Or`  Exi y g -> Exi x (pullQuantifiers (f     `Or` g))
      All x f `And` g       -> All x (pullQuantifiers (f     `And` inc g))
      f       `And` All y g -> All y (pullQuantifiers (inc f `And` g))
      All x f `Or` g        -> All x (pullQuantifiers (f     `Or` inc g))
      f       `Or` All y g  -> All y (pullQuantifiers (inc f `Or` g))
      Exi x f `And` g       -> Exi x (pullQuantifiers (f     `And` inc g))
      f       `And` Exi y g -> Exi y (pullQuantifiers (inc f `And` g))
      Exi x f `Or` g        -> Exi x (pullQuantifiers (f     `Or` inc g))
      f       `Or` Exi y g  -> Exi y (pullQuantifiers (inc f `Or` g))
      f                     -> f

-- Index manangement

-- | Increment all de Bruijn indices by one.
inc :: Formula -> Formula
inc = incAbove 0
  where
    incAbove n = \case
      v@Ind{indIndex = i} -> v{indIndex = if n <= i then i + 1 else i}
      All x f -> All x $ incAbove (n + 1) f
      Exi x f -> Exi x $ incAbove (n + 1) f
      f -> mapF (incAbove n) f

-- | Decrement all de Bruijn indices by one.
dec :: Formula -> Formula
dec = decAbove 0
  where
    decAbove n = \case
      v@Ind{indIndex = i} -> v{indIndex = if n <= i then i - 1 else i}
      All x f -> All x $ decAbove (n + 1) f
      Exi x f -> Exi x $ decAbove (n + 1) f
      f -> mapF (decAbove n) f


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
    dive (sc, dc, fs) (All x f) = dive (sc, dc + 1, fs . All x) f
    dive (sc, dc, fs) (Exi _ f) = dive (sc + 1, dc, fs) (dec $ instSk sc dc f)
    dive (sc, dc, fs) (Or  f g) =
      let (sc', _, fs') = dive (sc, dc, id) f in dive (sc', dc, fs . Or  fs') g
    dive (sc, dc, fs) (And f g) =
      let (sc', _, fs') = dive (sc, dc, id) f in dive (sc', dc, fs . And fs') g
    dive (sc, dc, fs) f = (sc, dc, fs f)

instSk :: Int -> Int -> Formula -> Formula
instSk skolemCnt dependencyCnt = dive 0
  where
    dive d (All x f) = All x $ dive (d + 1) f
    dive d (Exi x f) = Exi x $ dive (d + 1) f
    dive d Ind {indIndex = m} | d == m = skolemFunction d
    dive d f = mapF (dive d) f

    skolemFunction = mkTrm (SkolemId (skolemCnt)) (TermTask skolemCnt) . skolemArguments
    skolemArguments d = [Ind (i + d) Position.none | i <- [1..dependencyCnt] ]


-- specialization of formula: get rid of universal quantifiers

specialize :: Formula -> Formula
specialize = specCh (VarHole . Text.pack . show) 0

specCh :: (Int -> VariableName) -> Int -> Formula -> Formula
specCh mkVar = dive
  where
    dive n (All _ f) = dive (n + 1) $ inst (mkVar n) f
    dive n f = f


-- Conversion to CNF

transformToCNF :: Formula -> [[Formula]]
transformToCNF = simpCNF . specialize . prenex

simpCNF :: Formula -> [[Formula]]
simpCNF Top = [[]]
simpCNF Bot = []
simpCNF f = subsumptionCheck $ filter (not . isTrivial) $ pureCNF f
  where
    isTrivial :: [Formula] -> Bool
    isTrivial [] = False
    isTrivial (l:ls) = isTop l || any (ltTwins $ ltNeg l) ls || isTrivial ls

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
listEq _ _ = False

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
isSkolem Trm {trId = SkolemId _} = True
isSkolem _ = False
