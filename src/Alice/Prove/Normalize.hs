{-
Authors: Steffen Frerix (2017 - 2018)

Normalization of formulas.
-}



module Alice.Prove.Normalize where

import Alice.Data.Formula


import Data.List
import Control.Monad.State
import Debug.Trace



-- simplification : push down negation, replace implication and equivalence

simplify :: Formula -> Formula
simplify = mapF simplify . nbool . pushdown
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
pushdown (All _ (Imp (Tag HeadTerm Trm {trName = "=", trArgs = [_,t]} ) f))   = pushdown $ dec $ subst t "" $ inst "" f
pushdown (All _ (Iff (Tag HeadTerm eq@Trm {trName = "=", trArgs = [_,t]}) f)) = And (All "" (Or eq (Not f))) $ dec $ subst t "" $ inst "" f
pushdown f               = f


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

inc = increment 0
  where
    increment n (Ind i) = Ind (if n <= i then succ i else i)
    increment n (All x f)  = All x $ increment (succ n) f
    increment n (Exi x f)  = Exi x $ increment (succ n) f
    increment n f = mapF (increment n) f


-- skolemization

skolemize = fst . sklm 0


data SkState = SK { sk :: Int, tn :: Int}


sklm n f = runState (skolem f) $ SK n 0
  where
    skolem (All x f) = incCn >> skolem f >>= return . All x
    skolem (Exi _ f) = instSk f >>= skolem . dec
    skolem (Or  f g) = do st <- get; liftM2 Or  (skolem f) (modify (reSt st) >> skolem g)
    skolem (And f g) = do st <- get; liftM2 And (skolem f) (modify (reSt st) >> skolem g)
    skolem f = return f

    incCn = modify (\st -> st {tn = succ (tn st)})
    reSt st ost = ost { tn = tn st}

instSk :: Formula -> State SkState Formula
instSk f = do st <- get; let nf = instSk' (sk st) (tn st) f
              put $ st { sk = succ (sk st) }; return nf

instSk' :: Int -> Int -> Formula -> Formula
instSk' sk tn = dive 0
  where
    dive d (All x f) = All x $ dive (succ d) f
    dive d (Exi x f) = Exi x $ dive (succ d) f
    dive d (Ind m ) | d == m = skS d
    dive d f = mapF (dive d) f

    skS d = (zTrm skN skStr [Ind (i + d) | i <- [1..tn] ])

    skN = -20 - sk
    skStr = "tsk" ++ show sk



dec = decrement 0
  where
    decrement n (Ind i ) = Ind (if n <= i then pred i else i)
    decrement n (All x f)  = All x $ decrement (succ n) f
    decrement n (Exi x f)  = Exi x $ decrement (succ n) f
    decrement n f = mapF (decrement n) f




-- specialization of formula: get rid of universal quantifiers

specCh c = dive
  where
    dive n (All _ f) = dive (succ n) $ inst (c:show n) f
    dive n f = f

spec n = specCh '?' n


-- Conversion to CNF

simpcnf Top = [[]]
simpcnf Bot = []
simpcnf f = subsumptionCheck $ filter (not . trivial) $ purecnf f

purecnf :: Formula -> [[Formula]]
purecnf (And f g) = unionBy listEq (purecnf f) (purecnf g)
purecnf (Or f g)  = distrib (purecnf f) (purecnf g)
purecnf f = [[f]]


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

pullimp (Imp f (All x g)) = All x $ pullimp $ Imp (inc f) g
pullimp (Imp f (Imp g h)) = pullimp $ Imp (And f g) h
pullimp f = f


pushquants :: Formula -> Formula
pushquants (All x (And f g)) = And (pushquants $ All x f) (pushquants $ All x g)
pushquants (Exi x (Or  f g)) = Or  (pushquants $ Exi x f) (pushquants $ Exi x g)
pushquants (All x (Or  f g))
  | binding f = if binding g then All x $ Or (pushquants f) (pushquants g)
                             else Or (pushquants $ All x f) (pushquants $ dec g)
  | binding g = Or (pushquants $ dec f) (pushquants $ All x g)
  | otherwise = Or (pushquants $ dec f) (pushquants $ dec g)
pushquants (Exi x (And f g))
  | binding f = if binding g then Exi x $ And (pushquants f) (pushquants g)
                             else And (pushquants $ Exi x f) (pushquants $ dec g)
  | binding g = Or (pushquants $ dec f) (pushquants $ Exi x g)
  | otherwise = And (pushquants $ dec f) (pushquants $ dec g)
pushquants f = mapF pushquants f


binding = bin 0
  where
    bin n (Ind m) = n == m
    bin n (All _ f) = bin (succ n) f
    bin n (Exi _ f) = bin (succ n) f
    bin n f = anyF (bin n) f
