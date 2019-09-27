{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Various functions on formulas.
-}

module SAD.Data.Formula.Kit where

import Control.Monad
import Data.Maybe
import qualified Data.Map as M
import Data.Function (on)

import SAD.Data.Formula.Base
import SAD.Data.Tag
import SAD.Core.SourcePos
import SAD.Data.Text.Decl (Decl)
import qualified SAD.Data.Text.Decl as Decl
import SAD.Helpers
import SAD.Data.TermId

-- Alpha-beta normalization

-- | gets rid of top level negation, implication and equivalence if possible.
-- @albet (Not (Ind ..)) == Not (Ind ..)@
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

-- | Split a formula @Not (a \/ b) /\ c /\ ..@ into its conjuncts @[a,b,c,..]@
splitConjuncts :: Formula -> [Formula]
splitConjuncts = go . albet
  where
    go (And f g) = splitConjuncts f ++ splitConjuncts g
    go f = [f]

-- | remove all tags from a formula

deTag :: Formula -> Formula
deTag (Tag _ f) = deTag f
deTag f = mapF deTag f

-- | Boolean simplification
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

-- | perform boolean simplification through the whole formula
boolSimp :: Formula -> Formula
boolSimp f = bool $ mapF boolSimp f


-- Maybe quantification

-- | Maybe quantification handles quantification more efficiently in that it
-- possibly already simplifies formulas. Prototype example:
--     "exists x (x = t /\ P(x))" is replaced by "P(t)"
--     "forall x (x = t => P(x))" is replaced by "P(t)" 
--
-- In code:
-- @(mbExi "x" (And (Trm "=" [Var "x" [] noSourcePos, Var "t" [] noSourcePos] [] 0) (Var "x" [] noSourcePos))) == Just (Var "t" [] noSourcePos)@
-- Danger: We ignore the fact that @=@ is symmetric.
--
-- Arguments: the variable to look for (e.g. "x"), whether we are in an "existance" or an "all" case and the formula.
mbBind :: String -> Bool -> Formula -> Maybe Formula
mbBind v  = dive id
  where
    dive :: (Formula -> Formula) -> Bool -> Formula -> Maybe Formula
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

mbpExi, mbpAll :: (String, SourcePos) -> Formula -> Formula
mbpExi v f = fromMaybe (pExi v f) (mbBind (fst v) True f)
mbpAll v f = fromMaybe (pAll v f) (mbBind (fst v) False f)

mbdExi, mbdAll :: Decl -> Formula -> Formula
mbdExi v f = fromMaybe (dExi v f) (mbBind (Decl.name v) True f)
mbdAll v f = fromMaybe (dAll v f) (mbBind (Decl.name v) False f)


blAnd, blImp :: Formula -> Formula -> Formula
blAnd Top f = f; blAnd (Tag _ Top) f = f
blAnd f Top = f; blAnd f (Tag _ Top) = f
blAnd f g = And f g

blImp _ Top = Top; blImp _ (Tag _ Top) = Top
blImp Top f = f; blImp (Tag _ Top) f = f
blImp f g = Imp f g

pBlAll, pBlExi :: (String, SourcePos) -> Formula -> Formula
pBlAll _ Top = Top
pBlAll v f = All (Decl.nonParser v) f

pBlExi _ Top = Top
pBlExi v f = Exi (Decl.nonParser v) f

-- creation of formulas
zAll, zExi :: String -> Formula -> Formula
zAll v = bool . All (Decl.nonText v) . bind v
zExi v = bool . Exi (Decl.nonText v) . bind v

pAll, pExi :: (String, SourcePos) -> Formula -> Formula
pAll nm@(v, _) = pBlAll nm . bind v
pExi nm@(v, _) = pBlExi nm . bind v

dAll, dExi :: Decl -> Formula -> Formula
dAll dcl = bool . All dcl . bind (Decl.name dcl)
dExi dcl = bool . Exi dcl . bind (Decl.name dcl)

zIff, zOr :: Formula -> Formula -> Formula
zIff f g = And (Imp f g) (Imp g f)

zOr (Not f) g = Imp f g
zOr f g       = Or  f g

zVar :: String -> Formula
zVar v = pVar (v, noSourcePos)

pVar :: (String, SourcePos) -> Formula
pVar (v, pos) = Var v [] pos

zTrm :: TermId -> String -> [Formula] -> Formula
zTrm tId t ts = Trm t ts [] tId


-- creation of predefined functions and notions

zEqu :: Formula -> Formula -> Formula
zEqu t s  = zTrm EqualityId "=" [t,s]
zLess :: Formula -> Formula -> Formula
zLess t s = zTrm LessId "iLess" [t,s]
zThesis :: Formula
zThesis   = zTrm ThesisId "#TH#" []
zFun :: Formula -> Formula
zFun      = zTrm FunctionId "aFunction" . pure
zApp :: Formula -> Formula -> Formula
zApp f v  = zTrm ApplicationId "sdtlbdtrb" [f , v]
zDom :: Formula -> Formula
zDom      = zTrm DomainId "szDzozmlpdtrp" . pure
zSet :: Formula -> Formula
zSet      = zTrm SetId "aSet" . pure
zElem :: Formula -> Formula -> Formula
zElem x m = zTrm ElementId "aElementOf" [x,m]
zProd :: Formula -> Formula -> Formula
zProd m n = zTrm ProductId "szPzrzozdlpdtcmdtrp" [m, n]
zPair :: Formula -> Formula -> Formula
zPair x y = zTrm PairId "slpdtcmdtrp" [x,y]
zObj :: Formula -> Formula
zObj      = zTrm ObjectId "aObj" . pure -- this is a dummy for parsing purposes


-- quick checks of syntactic properties

isApplication :: Formula -> Bool
isApplication Trm {trId = ApplicationId} = True; isApplication _ = False
isTop :: Formula -> Bool
isTop Top = True; isTop _ = False
isBot :: Formula -> Bool
isBot Bot = True; isBot _ = False
isIff :: Formula -> Bool
isIff (Iff _ _) = True; isIff _ = False
isInd :: Formula -> Bool
isInd Ind{} = True; isInd _ = False
isVar :: Formula -> Bool
isVar Var{} = True; isVar _ = False
isTrm :: Formula -> Bool
isTrm Trm{} = True; isTrm _ = False
isEquality :: Formula -> Bool
isEquality t@Trm{} = trId t == EqualityId; isEquality _ = False
isThesis :: Formula -> Bool
isThesis t@Trm{} = trId t == ThesisId; isThesis _ = False
hasDEC :: Formula -> Bool
hasDEC (Tag EqualityChain _) = True; hasDEC _ = False
isExi :: Formula -> Bool
isExi (Exi _ _) = True; isExi _ = False
isAll :: Formula -> Bool
isAll (All _ _) = True; isAll _ = False
isConst :: Formula -> Bool
isConst t@Trm{} = null $ trArgs t; isConst Var{} = True; isConst _ = False
isNot :: Formula -> Bool
isNot (Not _) = True; isNot _ = False
isNotion :: Formula -> Bool
isNotion Trm {trName = 'a':_} = True; isNotion _ = False
isElem :: Formula -> Bool
isElem t = isTrm t && trId t == ElementId

-- Holes and slots

{- holes and slots act as placeholders during parsing, but do not appear
during the main verification procedure. -}
zHole, zSlot ::  Formula
zHole = zVar "?"; zSlot = zVar "!"

isHole, isSlot :: Formula -> Bool
isHole Var {trName = "?"} = True; isHole _ = False
isSlot Var {trName = "!"} = True; isSlot _ = False

substHole, substSlot :: Formula -> Formula -> Formula
substHole t = subst t "?"; substSlot t = subst t "!"

occursH, occursS :: Formula -> Bool
occursH = occurs zHole; occursS = occurs zSlot


-- | Replace @ObjectId@ Terms with @Top@
-- pseudotyping with "object"
removeObject :: Formula -> Formula
removeObject t@Trm {trId = tId}
  | tId == ObjectId = Top
  | otherwise = t
removeObject f = mapF removeObject f

-- functions for operating on literals
-- QUESTION: Why do we handle @Not t@ different from @t@?
isLiteral :: Formula -> Bool
isLiteral t@Trm{} = trId t /= EqualityId
isLiteral (Not t) = isTrm t
isLiteral _ = False

-- fetch the atomic formula used in a literal
ltAtomic :: Formula -> Formula
ltAtomic (Not t) = t; ltAtomic t = t

mbNot :: Formula -> Formula -> Formula
mbNot (Not _) = Not
mbNot _ = id

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

{- strip away a Tag on top level or after negation -}
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
tryToGetID :: Formula -> Maybe TermId
tryToGetID Trm {trId = n} = return n
tryToGetID _ = mzero


{- return free user named variables in a formula (without duplicateNames),
except those in vs -}
freePositions :: [String] -> Formula -> [(String, SourcePos)]
freePositions vs = nubOrdBy (compare `on` fst) . dive
  where
    dive f@Var {trName = u@('x':_)} = 
      (guard (u `notElem` vs) >> return (u, trPosition f)) ++ foldF dive f
    dive f = foldF dive f

free :: [String] -> Formula -> [String]
free vs = map fst . freePositions vs

{- return all free variables in a formula (without duplicateNames),
except those in vs -}
allFree :: [String] -> Formula -> [String]
allFree vs = nubOrd . dive
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