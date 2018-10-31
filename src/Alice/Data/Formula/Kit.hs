{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Various functions on formulas.
-}

module Alice.Data.Formula.Kit where

import Control.Monad
import Data.Maybe
import qualified Data.Map as M
import Data.List

import Alice.Data.Formula.Base
import Alice.Data.Tag

-- Alpha-beta normalization

{- gets rid of top level negation, implication and equivalence -}
albet :: Formula -> Formula
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
deAnd :: Formula -> [Formula]
deAnd = spl . albet
  where
    spl (And f g) = deAnd f ++ deAnd g
    spl f = [f]

{- remove all tags from a formula -}
deTag :: Formula -> Formula
deTag (Tag _ f) = deTag f
deTag f = mapF deTag f

-- Boolean simplification

bool :: Formula -> Formula
bool (All _ Top) = Top
bool (All _ Bot) = Bot
bool (Exi _ Top) = Top
bool (Exi _ Bot) = Bot
bool (Iff Top f) = f
bool (Iff f Top) = f
bool (Iff Bot f) = bool $ Not f
bool (Iff f Bot) = bool $ Not f
bool (Imp Top f) = f
bool (Imp _ Top) = Top
bool (Imp Bot _) = Top
bool (Imp f Bot) = bool $ Not f
bool (Or  Top _) = Top
bool (Or  _ Top) = Top
bool (Or  Bot f) = f
bool (Or  f Bot) = f
bool (And Top f) = f
bool (And f Top) = f
bool (And Bot _) = Bot
bool (And _ Bot) = Bot
bool (Tag _ Top) = Top
bool (Tag _ Bot) = Bot
bool (Not Top)   = Bot
bool (Not Bot)   = Top
bool f           = f

{- perform boolean simplification through the whole formula -}
boolSimp :: Formula -> Formula
boolSimp f = bool $ mapF boolSimp f


-- Maybe quantification

{- maybe quantification handles quantification more efficiently in that it
possibly already simplifies formulas. Prototype example:
       "exists x (x = t /\ P(x))" is replaced by "P(t)"
       "forall x (x = t => P(x))" is replaced by "P(t)" -}

mbBind :: String -> Bool -> Formula -> Maybe Formula
mbBind v  = dive id
  where
    dive c s (All u f) = dive (c . bool . All u) s f
    dive c s (Exi u f) = dive (c . bool . Exi u) s f
    dive c s (Tag a f) = dive (c . bool . Tag a) s f
    dive c s (Not f)   = dive (c . bool . Not) (not s) f
    dive c False (Imp f g) =
      dive (c . bool . (`Imp` g)) True f `mplus` 
      dive (c . bool . (f `Imp`)) False g
    dive c False (Or f g) = 
      dive (c . bool . (`Or` g)) False f `mplus`
      dive (c . bool . (f `Or`)) False g
    dive c True (And f g) = 
      dive (c . bool . (`And` g)) True f `mplus`
      dive (c . bool . (f `And`)) True g
    dive c True Trm {trName = "=", trArgs = [l@Var {trName = u}, t]}
      | u == v && not (occurs l t) && closed t = return $ subst t u (c Top)
    dive _ _ _ = mzero


mbExi, mbAll :: String -> Formula -> Formula
mbExi v f = fromMaybe (zExi v f) (mbBind v True f)
mbAll v f = fromMaybe (zAll v f) (mbBind v False f)


blAnd, blImp :: Formula -> Formula -> Formula
blAnd Top f = f; blAnd (Tag _ Top) f = f
blAnd f Top = f; blAnd f (Tag _ Top) = f
blAnd f g = And f g

blImp _ Top = Top; blImp _ (Tag _ Top) = Top
blImp Top f = f; blImp (Tag _ Top) f = f
blImp f g = Imp f g

blAll, blExi :: String -> Formula -> Formula
blAll _ Top = Top
blAll v f = All v f

blExi _ Top = Top
blExi v f = Exi v f

blNot :: Formula -> Formula
blNot (Not f) = f
blNot f = Not f

-- creation of formulas
zAll, zExi :: String -> Formula -> Formula
zAll v f = blAll v $ bind v f
zExi v f = blExi v $ bind v f

zIff, zOr :: Formula -> Formula -> Formula
zIff f g = And (Imp f g) (Imp g f)

zOr (Not f) g = Imp f g
zOr f g       = Or  f g

zVar :: String -> Formula
zVar v = Var v []

zTrm :: Int -> String -> [Formula] -> Formula
zTrm tId t ts = Trm t ts [] tId


-- creation of predefined functions and notions

zEqu t s  = zTrm equalityId "=" [t,s]
zLess t s = zTrm lessId "iLess" [t,s]
zThesis   = zTrm thesisId "#TH#" []
zFun      = zTrm functionId "aFunction" . pure
zApp f v  = zTrm applicationId "sdtlbdtrb" [f , v]
zDom      = zTrm domainId "szDzozmlpdtrp" . pure
zSet      = zTrm setId "aSet" . pure
zElem x m = zTrm elementId "aElementOf" [x,m]
zProd m n = zTrm productId "szPzrzozdlpdtcmdtrp" [m, n]
zPair x y = zTrm pairId "slpdtcmdtrp" [x,y]
zObj      = zTrm objectId "aObj" . pure -- this is a dummy for parsing purposes


-- predefined identifier

equalityId    =  -1 :: Int
lessId        =  -2 :: Int
thesisId      =  -3 :: Int
functionId    =  -4 :: Int
applicationId =  -5 :: Int
domainId      =  -6 :: Int
setId         =  -7 :: Int
elementId     =  -8 :: Int
productId     =  -9 :: Int
pairId        = -10 :: Int
objectId      = -11 :: Int
newId         = -15 :: Int -- temporary id given to newly introduced symbols


-- quick checks of syntactic properties

isApplication Trm {trId = -5} = True; isApplication _ = False
isTop Top = True; isTop _ = False
isBot Bot = True; isBot _ = False
isIff (Iff _ _) = True; isIff _ = False
isInd (Ind _ ) = True; isInd _ = False
isVar (Var _ _) = True; isVar _ = False
isTrm Trm{} = True; isTrm _ = False
isEquality t@Trm{} = trId t == equalityId; isEquality _ = False
isThesis t@Trm{} = trId t == thesisId; isThesis _ = False
hasDEC (Tag EqualityChain _) = True; hasDEC _ = False
isExi (Exi _ _) = True; isExi _ = False
isAll (All _ _) = True; isAll _ = False
isConst t@Trm{} = null $ trArgs t; isConst Var{} = True; isConst _ = False
isNot (Not _) = True; isNot _ = False
isNotion Trm {trName = 'a':_} = True; isNotion _ = False
isElem t = isTrm t && trId t == elementId

-- Holes and slots

{- holes and slots act as placeholders during parsing, but do not appear
during the main verification procedure. -}
zHole, zSlot ::  Formula
zHole = zVar "?"; zSlot = zVar "!"

isHole, isSlot :: Formula -> Bool
isHole (Var "?" _) = True; isHole _ = False
isSlot (Var "!" _) = True; isSlot _ = False

substHole, substSlot :: Formula -> Formula -> Formula
substHole t = subst t "?"; substSlot t = subst t "!"

occursH, occursS :: Formula -> Bool
occursH = occurs zHole; occursS = occurs zSlot

-- functions for operating on literals
isLiteral :: Formula -> Bool
isLiteral t@Trm{} = trId t /= equalityId
isLiteral (Not t) = isTrm t
isLiteral _ = False

-- fetch the atomic formula used in a literal
ltAtomic :: Formula -> Formula
ltAtomic (Not t) = t; ltAtomic t = t

ltArgs, ltInfo :: Formula -> [Formula]
ltArgs = trArgs . ltAtomic
ltInfo = trInfo . ltAtomic

ltId :: Formula -> Int
ltId   = trId   . ltAtomic

mbNot :: Formula -> Formula -> Formula
mbNot l = if isNot l then Not else id

ltNeg :: Formula -> Formula
ltNeg (Not t) = t
ltNeg t = Not t

ltTwins :: Formula -> Formula -> Bool
ltTwins (Not f) (Not g) = twins f g
ltTwins f g = twins f g

-- compare and match

{- checks for syntactic equality of literals modulo instantiation of the
placeholder token ThisT with the term t -}
infoTwins :: Formula -> Formula -> Formula -> Bool
infoTwins t = dive
  where
    dive (Not f) (Not g) = dive f g
    dive t@Trm{} s@Trm{} | trId t == trId s = pairs (trArgs t) (trArgs s)
    dive _ _ = False

    pairs (tr:ts) (sr:ss) = case (tr,sr) of
      (ThisT, ThisT) -> pairs ts ss
      (ThisT, f)     -> twins t f && pairs ts ss
      (f, ThisT)     -> twins t f && pairs ts ss
      (f, g)         -> twins f g && pairs ts ss
    pairs [] [] = True
    pairs _ _ = False


{- match a formula with another formula and return the substitution.
Only variables whose name begins with a '?' are considered matchable. 
All others are treated like constants. -}
match :: (MonadPlus m) => Formula -> Formula -> m (Formula -> Formula)
match Var {trName = x@('?':_)} t = return $ subst t x
match Var {trName = x} Var {trName = y} | x == y = return id
match t@Trm{} s@Trm{} | trId t == trId s = pairs (trArgs t) (trArgs s)
  where
    pairs (p:ps) (q:qs) = do
      sb <- pairs ps qs
      sc <- match (sb p) q
      return $ sc . sb
    pairs [] [] = return id
    pairs _ _   = mzero
match _ _ = mzero

-- Misc stuff

{- strip away a Tag on top level or after neation -}
strip :: Formula -> Formula
strip (Tag _ f) = strip f
strip (Not f)   = Not $ strip f
strip f         = f


guardElem :: [String] -> String -> [String]
guardElem vs v    = guard (v `elem` vs) >> return v

guardNotElem :: [String] -> String -> [String]
guardNotElem vs v = guard (v `notElem` vs) >> return v

{- extracts all duplicateNames (with multiplicity) from a list -}
duplicateNames :: [String] -> [String]
duplicateNames (v:vs) = guardElem vs v `mplus` duplicateNames vs
duplicateNames _      = mzero

{- safe identifier extraction -}
tryToGetID :: Formula -> Maybe Int
tryToGetID Trm {trId = n} = return n
tryToGetID _ = mzero


{- return free user named variables in a formula (without duplicateNames),
except those in vs -}
free :: [String] -> Formula -> [String]
free vs = nub . dive
  where
    dive f@Var {trName = u@('x':_)} = guardNotElem vs u ++ foldF dive f
    dive f = foldF dive f

{- return all free variables in a formula (without duplicateNames),
except those in vs -}
allFree :: [String] -> Formula -> [String]
allFree vs = nub . dive
  where
    dive f@Var {trName = u} = guardNotElem vs u ++ foldF dive f
    dive f = foldF dive f


{- universal closure of a formula -}
uClose :: [String] -> Formula -> Formula
uClose ls f = let vs = allFree ls f in foldr zAll f vs


-- substitutions as maps

{- apply a substitution that is represented as a finite partial map -}
applySb :: M.Map String Formula -> Formula -> Formula
applySb mp vr@Var {trName = v} = case M.lookup v mp of 
  Just t  -> t
  Nothing -> vr
applySb mp t = mapF (applySb mp) t

{- subsitution is also applied to the evidence for a term -}
infoSub :: (Formula -> Formula) -> Formula -> Formula
infoSub sb t@Trm{} = t {
  trArgs = map (infoSub sb) $ trArgs t, 
  trInfo = map sb $ trInfo t}
infoSub sb v@Var{} = sb v
infoSub sb f = mapF (infoSub sb) f

-- control variable names

{- changes the prefix of a variable name -}
fromTo :: Char -> Char -> Formula -> Formula
fromTo c1 c2 v@Var {trName = c':rst} | c' == c1 = v {trName = c2:rst}
fromTo c1 c2 f = mapF (fromTo c1 c2) f