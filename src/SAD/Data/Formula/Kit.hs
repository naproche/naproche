{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Various functions on formulas.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Formula.Kit where

import Control.Monad
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import SAD.Data.Formula.Base
import SAD.Data.Tag
import SAD.Core.SourcePos
import SAD.Data.Text.Decl
import SAD.Data.Terms
import SAD.Data.VarName

import qualified Data.Map as Map

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
-- @(mbExi "x" (And (Trm TermEquality [Var "x" [] noSourcePos, Var "t" [] noSourcePos] [] 0) (Var "x" [] noSourcePos))) == Just (Var "t" [] noSourcePos)@
-- Danger: We ignore the fact that @=@ is symmetric.
--
-- Arguments: the variable to look for (e.g. "x"), whether we are in an "existence" or an "all" case and the formula.
mbBind :: VariableName -> Bool -> Formula -> Maybe Formula
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
    dive c True Trm {trmName = TermEquality, trmArgs = [l@Var {varName = u}, t]}
      | u == v && not (l `occursIn` t) && isClosed t = return $ subst t u (c Top)
    dive _ _ _ = mzero


mbExi, mbAll :: VariableName -> Formula -> Formula
mbExi v f = fromMaybe (mkExi v f) (mbBind v True f)
mbAll v f = fromMaybe (mkAll v f) (mbBind v False f)

mbpExi, mbpAll :: PosVar -> Formula -> Formula
mbpExi v f = fromMaybe (pExi v f) (mbBind (posVarName v) True f)
mbpAll v f = fromMaybe (pAll v f) (mbBind (posVarName v) False f)

mbdExi, mbdAll :: Decl -> Formula -> Formula
mbdExi v f = fromMaybe (dExi v f) (mbBind (declName v) True f)
mbdAll v f = fromMaybe (dAll v f) (mbBind (declName v) False f)


blAnd, blImp :: Formula -> Formula -> Formula
blAnd Top f = f; blAnd (Tag _ Top) f = f
blAnd f Top = f; blAnd f (Tag _ Top) = f
blAnd f g = And f g

blImp _ Top = Top; blImp _ (Tag _ Top) = Top
blImp Top f = f; blImp (Tag _ Top) f = f
blImp f g = Imp f g

pBlAll, pBlExi :: PosVar -> Formula -> Formula
pBlAll _ Top = Top
pBlAll v f = All (positionedDecl v) f

pBlExi _ Top = Top
pBlExi v f = Exi (positionedDecl v) f

-- creation of formulas
mkAll, mkExi :: VariableName -> Formula -> Formula
mkAll v = bool . All (newDecl v) . bind v
mkExi v = bool . Exi (newDecl v) . bind v

pAll, pExi :: PosVar -> Formula -> Formula
pAll nm@(PosVar v _) = pBlAll nm . bind v
pExi nm@(PosVar v _) = pBlExi nm . bind v

dAll, dExi :: Decl -> Formula -> Formula
dAll dcl = bool . All dcl . bind (declName dcl)
dExi dcl = bool . Exi dcl . bind (declName dcl)

zIff, zOr :: Formula -> Formula -> Formula
zIff f g = And (Imp f g) (Imp g f)

zOr (Not f) g = Imp f g
zOr f g       = Or  f g

mkVar :: VariableName -> Formula
mkVar v = pVar $ PosVar v noSourcePos

-- | Given a variable name with position data, creates a formula consisting of just
-- a that variable.
pVar :: PosVar -> Formula
pVar (PosVar v pos) = Var v [] pos

mkTrm :: TermId -> TermName -> [Formula] -> Formula
mkTrm tId t ts = Trm t ts [] tId


-- creation of predefined functions and notions

mkEquality :: Formula -> Formula -> Formula
mkEquality t s  = mkTrm EqualityId TermEquality [t,s]
mkLess :: Formula -> Formula -> Formula
mkLess t s = mkTrm LessId TermLess [t,s]
mkThesis :: Formula
mkThesis   = mkTrm ThesisId TermThesis []
mkFun :: Formula -> Formula
mkFun      = mkTrm FunctionId termFunction . pure
mkApp :: Formula -> Formula -> Formula
mkApp f v  = mkTrm ApplicationId termApplication [f , v]
mkDom :: Formula -> Formula
mkDom      = mkTrm DomainId termDomain . pure
mkSet :: Formula -> Formula
mkSet      = mkTrm SetId termSet . pure
mkElem :: Formula -> Formula -> Formula
mkElem x m = mkTrm ElementId termElement [x,m]
mkProd :: Formula -> Formula -> Formula
mkProd m n = mkTrm ProductId termProduct [m, n]
mkPair :: Formula -> Formula -> Formula
mkPair x y = mkTrm PairId termPair [x,y]
mkObj :: Formula -> Formula
mkObj      = mkTrm ObjectId termObject . pure -- this is a dummy for parsing purposes


-- quick checks of syntactic properties

isApplication :: Formula -> Bool
isApplication Trm {trmId = ApplicationId} = True; isApplication _ = False
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
hasDEC :: Formula -> Bool
hasDEC (Tag EqualityChain _) = True; hasDEC _ = False
isExi :: Formula -> Bool
isExi (Exi _ _) = True; isExi _ = False
isAll :: Formula -> Bool
isAll (All _ _) = True; isAll _ = False
isConst :: Formula -> Bool
isConst t@Trm{} = null $ trmArgs t; isConst Var{} = True; isConst _ = False
isNot :: Formula -> Bool
isNot (Not _) = True; isNot _ = False

isNotion :: Formula -> Bool
isNotion Trm {trmName = TermNotion _} = True
isNotion _ = False

isElem :: Formula -> Bool
isElem t = isTrm t && trmId t == ElementId

-- Holes and slots

occursH, occursS :: Formula -> Bool
occursH = ((mkVar (VarHole "")) `occursIn`)
occursS = ((mkVar VarSlot) `occursIn`)


-- | Replace @ObjectId@ Terms with @Top@
-- pseudotyping with "object"
removeObject :: Formula -> Formula
removeObject t@Trm {trmId = tId}
  | tId == ObjectId = Top
  | otherwise = t
removeObject f = mapF removeObject f

-- functions for operating on literals
-- QUESTION: Why do we handle @Not t@ different from @t@?
isLiteral :: Formula -> Bool
isLiteral t@Trm{} = trmId t /= EqualityId
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
    dive t@Trm{} s@Trm{} | trmId t == trmId s = pairs (trmArgs t) (trmArgs s)
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
match Var {varName = x@(VarHole _)} t = return $ subst t x
match Var {varName = x} Var {varName = y} | x == y = return id
match t@Trm{} s@Trm{} | trmId t == trmId s = pairs (trmArgs t) (trmArgs s)
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

{- extracts all duplicateNames (with multiplicity) from a list -}
duplicateNames :: Ord a => [a] -> [a]
duplicateNames ls = concatMap (\(k,a) -> replicate (a-1) k)
                  $ Map.toList $ Map.fromListWith (+) $ zip ls $ repeat (1::Int)

free :: IsVar a => Formula -> FV a
free f@Var {varName = u@(VarConstant _)} = unitFV u (varPosition f) <> foldF free f
free f = foldF free f

{- return all free variables in a formula (without duplicateNames),
except those in vs -}
allFree :: IsVar a => Formula -> FV a
allFree f@Var {varName = u} = unitFV u (varPosition f) <> foldF allFree f
allFree f = foldF allFree f


{- universal closure of a formula -}
universialClosure :: Set VariableName -> Formula -> Formula
universialClosure ls f = foldr mkAll f $ Set.toList $ fvToVarSet
  $ allFree f `excludeSet` ls


-- Substitution with substitution maps

-- | Apply a substitution that is represented as a finite partial map.
applySub :: Map.Map VariableName Formula -> Formula -> Formula
-- TODO: Should @applySub sub@ be @id@ when the variable lookup fails?
applySub sub vr@Var{varName = v} = fromMaybe vr $ Map.lookup v sub
applySub sub t = mapF (applySub sub) t

-- | Subsitution is also applied to the evidence for a term
infoSub :: (Formula -> Formula) -> Formula -> Formula
infoSub sb t@Trm{} = t {
  trmArgs = map (infoSub sb) $ trmArgs t,
  trmInfo = map sb $ trmInfo t}
infoSub sb v@Var{} = sb v
infoSub sb f = mapF (infoSub sb) f
