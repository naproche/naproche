-- |
--Authors: Andrei Paskevich (2001 - 2008),
--         Steffen Frerix (2017 - 2018)
--
-- Various functions on formulas.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Formula.Kit where

import Control.Monad
import Data.Maybe
import Data.Map qualified as Map

import SAD.Data.Formula.Base
import SAD.Data.Tag
import SAD.Data.Text.Decl
import SAD.Data.Terms
import SAD.Data.VarName

import Isabelle.Position qualified as Position


-- * Alpha-beta normalization

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


-- * Maybe quantification

-- | Maybe quantification handles quantification more efficiently in that it
-- possibly already simplifies formulas. Prototype example:
--     "exists x (x = t /\ P(x))" is replaced by "P(t)"
--     "forall x (x = t => P(x))" is replaced by "P(t)"
--
-- In code:
-- @(mbExi "x" (And (Trm TermEquality [Var "x" [] Position.none, Var "t" [] Position.none] [] 0) (Var "x" [] Position.none))) == Just (Var "t" [] Position.none)@
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


-- * Creation of formulas

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
mkVar v = pVar $ PosVar v Position.none

-- | Given a variable name with position data, creates a formula consisting of just
-- a that variable.
pVar :: PosVar -> Formula
pVar (PosVar v pos) = Var v [] pos

mkTrm :: TermId -> TermName -> [Formula] -> Formula
mkTrm tId t ts = Trm t ts [] tId


-- * Creation of predefined functions and notions

-- @mkEquality s t@ creates a formula of the form @s = t@
mkEquality :: Formula -> Formula -> Formula
mkEquality s t = mkTrm EqualityId TermEquality [s, t]

-- @mkLess s t@ creates a formula of the form @iLess(s,t)@
mkLess :: Formula -> Formula -> Formula
mkLess s t = mkTrm LessId TermLess [s, t]

-- @mkThesis@ creates a formula of the form @thesis@
mkThesis :: Formula
mkThesis = mkTrm ThesisId TermThesis []

-- @mkFunction t@ creates a formula of the form @aFunction(t)@
mkFunction :: Formula -> Formula
mkFunction t = mkTrm FunctionId termFunction [t]

-- @mkMap t@ creates a formula of the form @aMap(t)@
mkMap :: Formula -> Formula
mkMap t = mkTrm MapId termMap [t]

-- @mkApp s t@ creates a formula of the form @s(t)@
mkApp :: Formula -> Formula -> Formula
mkApp s t = mkTrm ApplicationId termApplication [s, t]

-- @mkDom t@ creates a formula of the form @Dom(t)@
mkDom :: Formula -> Formula
mkDom t = mkTrm DomainId termDomain [t]

-- @mkSet t@ creates a formula of the form @aSet(t)@
mkSet :: Formula -> Formula
mkSet t = mkTrm SetId termSet [t]

-- @mkClass t@ creates a formula of the form @aClass(t)@
mkClass :: Formula -> Formula
mkClass t = mkTrm ClassId termClass [t]

-- @mkElem s t@ creates a formula of the form @aElementOf(s,t)@
mkElem :: Formula -> Formula -> Formula
mkElem s t = mkTrm ElementId termElement [s, t]

-- @mkPair s t@ creates a formula of the form @(s,t)@
mkPair :: Formula -> Formula -> Formula
mkPair s t = mkTrm PairId termPair [s, t]

-- @mkObject t@ creates a formula of the form @aObject(t)@
mkObject :: Formula -> Formula
mkObject t = mkTrm ObjectId termObject [t]


-- * Cquick checks of syntactic properties

-- ** Composite formulas

-- | Check whether a formula is of the form @truth@
isTop :: Formula -> Bool
isTop Top = True
isTop _ = False

-- | Check whether a formula is of the form @falsity@
isBot :: Formula -> Bool
isBot Bot = True
isBot _ = False

-- | Check whether a formula is of the form @not ...@
isNot :: Formula -> Bool
isNot (Not _) = True
isNot _ = False

-- | Check whether a formula is of the form @... and ...@
isAnd :: Formula -> Bool
isAnd (_ `And` _) = True
isAnd _ = False

-- | Check whether a formula is of the form @... or ...@
isOr :: Formula -> Bool
isOr (_ `Or` _) = True
isOr _ = False

-- | Check whether a formula is of the form @... implies ...@
isImp :: Formula -> Bool
isImp (_ `Imp` _) = True
isImp _ = False

-- | Check whether a formula is of the form @... iff ...@
isIff :: Formula -> Bool
isIff (_ `Iff` _) = True
isIff _ = False

-- | Check whether a formula is of the form @exists ... such that ...@
isExi :: Formula -> Bool
isExi (Exi _ _) = True
isExi _ = False

-- | Check whether a formula is of the form @for all ... we have ...@
isAll :: Formula -> Bool
isAll (All _ _) = True
isAll _ = False


-- ** Atomic formulas

-- | Check whether a formula is of the form @aObject(...)@
isObject :: Formula -> Bool
isObject t = isTrm t && trmId t == ObjectId

-- | Check whether a formula is of the form @aClass(...)@
isClass :: Formula -> Bool
isClass t = isTrm t && trmId t == ClassId

-- | Check whether a formula is of the form @aSet(...)@
isSet :: Formula -> Bool
isSet t = isTrm t && trmId t == SetId

-- | Check whether a formula is of the form @aMap(...)@
isMap :: Formula -> Bool
isMap t = isTrm t && trmId t == MapId

-- | Check whether a formula is of the form @aFunction(...)@
isFunction :: Formula -> Bool
isFunction t = isTrm t && trmId t == FunctionId

-- | Check whether a formula is of the form @aElementOf(...)@
isElem :: Formula -> Bool
isElem t = isTrm t && trmId t == ElementId

-- | Check whether a formula is of the form @...(...)@
isApplication :: Formula -> Bool
isApplication t = isTrm t && trId t == ApplicationId

-- | Check whether a formula is of the form @Dom(...)@
isDom :: Formula -> Bool
isDom t = isTrm t && trmId t == DomainId

-- | Check whether a formula is of the form @(...,...)@
isPair :: Formula -> Bool
isPair t = isTrm t && trmId t == PairId

-- | Check whether a formula is of the form @iLess(...)@
isLess :: Formula -> Bool
isLess t = isTrm t && trmId t == LessId

-- | Check whether a formula is of the form @thesis@
isThesis :: Formula -> Bool
isThesis t = isTrm t && trmId t == ThesisId


-- ** Misc

isInd :: Formula -> Bool
isInd Ind{} = True
isInd _ = False

isVar :: Formula -> Bool
isVar Var{} = True
isVar _ = False

isTrm :: Formula -> Bool
isTrm Trm{} = True
isTrm _ = False

hasDEC :: Formula -> Bool
hasDEC (Tag EqualityChain _) = True
hasDEC _ = False

hasDMK :: Formula -> Bool
hasDMK (Tag GenericMark _ ) = True
hasDMK _ = False

isConst :: Formula -> Bool
isConst t@Trm{} = null $ trmArgs t
isConst Var{} = True
isConst _ = False

isNotion :: Formula -> Bool
isNotion Trm {trmName = TermNotion _} = True
isNotion _ = False


-- * Holes and slots

occursH, occursS :: Formula -> Bool
occursH = (mkVar (VarHole "") `occursIn`)
occursS = (mkVar VarSlot `occursIn`)


-- * Functions for operating on literals

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


-- * Compare and match

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


-- * Misc stuff

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


-- * Substitution with substitution maps

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
