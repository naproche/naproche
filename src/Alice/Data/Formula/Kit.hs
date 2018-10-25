{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Various functions on formulas.
-}

module Alice.Data.Formula.Kit where

import Control.Monad
import Data.Maybe
import qualified Data.IntMap.Strict as IM
import qualified Data.Map as M
import Debug.Trace
import Data.List

import Alice.Data.Formula.Base
import Alice.Data.Tag

-- Alpha-beta normalization

{- gets rid of top level negation, implication and equivalence -}
albet (Iff f g)       = zIff f g
albet (Imp f g)       = Or (Not f) g
albet (Not (All v f)) = Exi v $ Not f
albet (Not (Exi v f)) = All v $ Not f
albet (Not (Iff f g)) = albet $ Not $ zIff f g
albet (Not (Imp f g)) = And f (Not g)
albet (Not (And f g)) = Or (Not f) (Not g)
albet (Not (Or f g))  = And (Not f) (Not g)
albet (Not (Not f))   = albet f
albet (Not Top)       = Bot
albet (Not Bot)       = Top
albet (Tag t f)       = Tag t $ albet f
albet f               = f

{- split a formula into its conjucts -}
deAnd = spl . albet
  where
    spl (And f g) = deAnd f ++ deAnd g
    spl f = [f]

{- split a formula into its disjuncts -}
deOr  = spl . albet
  where
    spl (Or f g)  = deOr f ++ deOr g
    spl f = [f]

{- remove all tags from a formula -}
deTag (Tag _ f) = deTag f
deTag f = mapF deTag f

-- Boolean simplification

bool (All _ Top)  = Top
bool (All _ Bot)  = Bot
bool (Exi _ Top)  = Top
bool (Exi _ Bot)  = Bot
bool (Iff Top f)  = f
bool (Iff f Top)  = f
bool (Iff Bot f)  = bool $ Not f
bool (Iff f Bot)  = bool $ Not f
bool (Imp Top f)  = f
bool (Imp _ Top)  = Top
bool (Imp Bot _)  = Top
bool (Imp f Bot)  = bool $ Not f
bool (Or  Top _)  = Top
bool (Or  _ Top)  = Top
bool (Or  Bot f)  = f
bool (Or  f Bot)  = f
bool (And Top f)  = f
bool (And f Top)  = f
bool (And Bot _)  = Bot
bool (And _ Bot)  = Bot
bool (Tag _ Top)  = Top
bool (Tag _ Bot)  = Bot
bool (Not Top)    = Bot
bool (Not Bot)    = Top
bool f            = f

neg (Not f) = f
neg f = bool $ Not f

{- perform boolean simplification through the whole formula -}
bool_simp f = bool $ mapF bool_simp f


-- Maybe quantification

{- maybe quantification handles quantification more efficiently in that it possibly
   already simplifies formulas. Prototype example:
       "exists x (x = t /\ P(x))" is replaced by "P(t)"
       "forall x (x = t => P(x))" is replaced by "P(t)" -}

mbBind v  = dive id
  where
    dive c s (All u f)  = dive (c . bool . All u) s f
    dive c s (Exi u f)  = dive (c . bool . Exi u) s f
    dive c s (Tag a f)  = dive (c . bool . Tag a) s f
    dive c s (Not f)    = dive (c . bool . Not) (not s) f
    dive c False (Imp f g)  = dive (c . bool . (`Imp` g)) True f
                      `mplus` dive (c . bool . (f `Imp`)) False g
    dive c False (Or f g)   = dive (c . bool . (`Or` g)) False f
                      `mplus` dive (c . bool . (f `Or`)) False g
    dive c True (And f g)   = dive (c . bool . (`And` g)) True f
                      `mplus` dive (c . bool . (f `And`)) True g
    dive c True Trm {trName = "=", trArgs = [l@Var {trName = u}, t]}
      | u == v && not (occurs l t) && closed t
                = return $ subst t u (c Top)
    dive _ _ _  = mzero

mbExi v f = fromMaybe (zExi v f) (mbBind v True f)
mbAll v f = fromMaybe (zAll v f) (mbBind v False f)

blAnd Top f = f; blAnd (Tag _ Top) f = f
blAnd f Top = f; blAnd f (Tag _ Top) = f
blAnd f g = And f g

blImp f Top = Top; blImp f (Tag _ Top) = Top
blImp Top f = f; blImp (Tag _ Top) f = f
blImp f g = Imp f g

blAll v Top = Top
blAll v f = All v f

blExi v Top = Top
blExi v f = Exi v f

blNot (Not f) = f
blNot f = Not f

-- Useful macros

zAll v f  = blAll v $ bind v f
zExi v f  = blExi v $ bind v f

zIff f g  = And (Imp f g) (Imp g f)

zOr (Not f) g = Imp f g
zOr f g       = Or  f g

zVar v    = Var v []
zTrm tId t ts = Trm t ts [] tId
zThesis   = zTrm (-3) "#TH#" []
zEqu t s  = zTrm (-1) "=" [t,s]
zLess t s = zTrm (-2) "iLess" [t,s]
zSSS trId s ts = zTrm trId ('c':'S':':':s) ts

funId = -4 :: Int
zFun f = zTrm (-4) "aFunction" [f]
zApp f v = zTrm (-5) "sdtlbdtrb" [f , v]
zDom f = zTrm (-6) "szDzozmlpdtrp" [f]

sEqu x y = let v = zVar "" in zAll "" (Iff (zElem v x) (zElem v y)) -- macro for set equality

setId = (-7) :: Int
zSet m = zTrm (-7) "aSet" [m]
zElem x m = zTrm (-8) "aElementOf" [x,m]
elmId = (-8) :: Int
zProd m n = zTrm (-9) "szPzrzozdlpdtcmdtrp" [m, n]
zPair x y = zTrm (-10) "slpdtcmdtrp" [x,y]
zObj x = zTrm (-11) "aObj" [x] -- this is a dummy for parsing purposes

pairId = -10 :: Int
appId = -5 :: Int
objId = -11 :: Int
domId = (-6) :: Int

newId = (-15) :: Int -- the temporary id given to symbols that are being introduced

dhdId Trm {trName = "=", trArgs = [_,t]} = trId t
dhdId t = trId t

-- quick checks of syntactic properties

isApp Trm {trId = -5} = True
isApp _ = False

isTop Top = True
isTop _   = False

isBot Bot = True
isBot _   = False

isIff (Iff _ _) = True
isIff _         = False

isInd (Ind _ ) = True
isInd _         = False

isVar (Var _ _) = True
isVar _         = False

isTrm (Trm _ _ _ _) = True
isTrm _             = False

isEqu (Trm "=" [_,_] _ _) = True
isEqu _                   = False

isThesis (Trm "#TH#" [] _ _)  = True
isThesis _                    = False

isSSS (Trm ('c':'S':':':_) _ _ _) = True
isSSS _                           = False

hasDEC (Tag DEC _) = True
hasDEC _ = False

isExi (Exi _ _) = True
isExi _ = False

isAll (All _ _) = True
isAll _ = False

isConst (Trm _ [] _ _) = True
isConst (Var _ _)      = True
isConst _              = False

isNot (Not _) = True
isNot f = False

isNeq (Not (Trm  "=" _ _ _)) = True
isNeq f = False

isNtn Trm {trName = 'a':_} = True
isNtn _ = False


isElem t = isTrm t && trId t == elmId
-- Holes and slots

{- holes and slots act as placeholders during parsing, but do not appear
   during the main verification procedure. -}
zHole = zVar "?"
zSlot = zVar "!"

isHole (Var "?" _)  = True
isHole _            = False

isSlot (Var "!" _)  = True
isSlot _            = False

substH t  = subst t "?"
substS t  = subst t "!"

occursH = occurs zHole
occursS = occurs zSlot

fromTo c1 c2 v@Var {trName = c':rst} | c' == c1 = v {trName = c2:rst}
fromTo c1 c2 f = mapF (fromTo c1 c2) f
-- functions for operating on literals

isLtrl Trm {trName = "="} = False
isLtrl (Not t) = isTrm t
isLtrl t       = isTrm t

predSymb (Not t) = t
predSymb t = t

ltArgs = trArgs . predSymb
ltId t  = trId   . predSymb $ t
ltInfo = trInfo . predSymb

mbNot l = if isNot l then Not else id

ltNeg (Not t) = t
ltNeg t = Not t


ltTwins (Not f) (Not g) = twins f g
ltTwins f g = twins f g


{- checks for syntactic equality modulo instantiation of the
   placeholder token ThisT with the term t -}
infoTwins t = dive
  where
    dive (Not f) (Not g) = dive f g
    dive Trm {trArgs = ts, trId = n} Trm {trArgs = ss, trId = m} | m == n = pairs ts ss
    dive _ _ = False

    pairs (tr:ts) (sr:ss) = let b = pairs ts ss
                             in case (tr,sr) of
                               (ThisT, ThisT) -> b
                               (ThisT, f) -> twins t f && b
                               (f, ThisT) -> twins t f && b
                               (f, g) -> twins f g && b
    pairs [] [] = True
    pairs _ _ = False

-- Misc stuff

{- strip away a Tag on top level or after neation -}
strip (Tag _ f) = strip f
strip (Not f)   = Not $ strip f
strip f         = f

infilt vs v = guard (v `elem` vs) >> return v
nifilt vs v = guard (v `notElem` vs) >> return v

{- extracts all duplicates (with multiplicity) from a list -}
dups (v:vs) = infilt vs v `mplus` dups vs
dups _      = mzero

{- safe identifier extraction -}
tryToGetID :: Formula -> Maybe Int
tryToGetID Trm {trId = n} = return n
tryToGetID _ = mzero

{- match a formula with another formula and return the substitution. Only variables
   whose name begins with a '?' are considered matchable. All others are treated
   like constants. -}
match :: (MonadPlus m) => Formula -> Formula -> m (Formula -> Formula)
match Var {trName = v@('?':_)} t       = return  $ subst t v           -- an instantiable variable can simply be substituted for
match Var {trName = u} Var {trName = v}    | u == v  = return id       -- variables considered as constants must be the same
match Trm {trArgs = ps, trId = n} Trm {trArgs = qs, trId = m} | n == m  = pairs ps qs
  where -- two terms match if their identifiers are the same and their arguments can be consistently matched
    pairs (p:ps) (q:qs) = do  sb <- pairs ps qs
                              sc <- match (sb p) q   -- we apply sb to p here to ensure a consistent matching
                              return $ sc . sb
    pairs [] []         = return id
    pairs _ _           = mzero
match _ _         = mzero                             -- if we can't match, we fail


{-extract the headatom from a sigext or definition -}
hdatom (All _ f) = hdatom f
hdatom (Imp  (Tag DHD t) _) = t
hdatom (Iff  (Tag DHD t) _) = t
hdatom (Imp f g) = hdatom g

{- extract the headterm from a sigext or definition -}
hdterm f = case hdatom f of Trm {trName = "=", trArgs = [_,t]} -> t; t -> t

{- return free user named variables in a formula (without duplicates) except those in vs -}
free vs = nub . dive
  where
    dive f@Var {trName = u@('x':_)}  = nifilt vs u ++ foldF dive f
    dive f                    = foldF dive f

{- return all free variables in a formula (without duplicates) except those in vs -}
allFree vs = nub . dive
  where
    dive f@Var {trName = u} = nifilt vs u ++ foldF dive f
    dive f = foldF dive f

onlyFree c vs = nub. dive
  where
    dive f@Var {trName = u@(c:_)} = nifilt vs u ++ foldF dive f
    dive f = foldF dive f

{- universal closure of a formula -}
uClose ls f = let vs = allFree ls f in foldr zAll f vs

{- checks whether the formula t occurs anywhere in the formula f -}
occurs :: Formula -> Formula -> Bool
occurs t  = dive
  where
    dive f  = twins t f || anyF dive f



renull (All _ f)  = All "" f
renull (Exi _ f)  = Exi "" f
renull f          = mapF renull f

total_renull (All _ f) = All "" $ total_renull f
total_renull (Exi _ f) = Exi "" $ total_renull f
total_renull f = mapF total_renull f


-- substitutions as maps

{- apply a substitution that is represented as a finite partial map -}
applySb :: M.Map String Formula -> Formula -> Formula
applySb mp vr@Var {trName = v}
  = case M.lookup v mp of Just t -> t; Nothing -> vr
applySb mp t = mapF (applySb mp) t


infoSub :: (Formula -> Formula) -> Formula -> Formula -- a substitution that also extends to the evidence for the term
infoSub sb t@Trm {trArgs = ts, trInfo = is}
  = t {trArgs = map (infoSub sb) ts, trInfo = map sb is}
infoSub sb v@Var{} = sb v
infoSub sb f = mapF (infoSub sb) f
