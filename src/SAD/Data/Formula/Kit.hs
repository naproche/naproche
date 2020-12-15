{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Various functions on formulas.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Formula.Kit
  ( mkExi, blAnd, mkAll, blImp, mkTrm, mkFun, mkSet, mkElem, mkObj, mkVar
  , mkPair, mkDom, mkApp, pVar, free, allFree, duplicateNames
  , isNotion, isTrm, occursH, dAll, mkEquality, mkThesis
  , mbdExi, dExi, strip, isVar, occursS, removeObject, mkLess)
  where

import Control.Monad
import Data.Maybe

import SAD.Data.Formula.Base
import PIDE.SourcePos
import SAD.Data.Text.Decl
import SAD.Data.Terms
import SAD.Data.VarName

import qualified Data.Map as Map

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
-- Arguments: the variable to look for (e.g. "x"), whether we are in an "existance" or an "all" case and the formula.
mbBind :: VarName -> Bool -> Formula -> Maybe Formula
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

mbdExi :: Decl -> Formula -> Formula
mbdExi v f = fromMaybe (dExi v f) (mbBind (declName v) True f)


blAnd, blImp :: Formula -> Formula -> Formula
blAnd Top f = f; blAnd (Tag _ Top) f = f
blAnd f Top = f; blAnd f (Tag _ Top) = f
blAnd f g = And f g

blImp _ Top = Top; blImp _ (Tag _ Top) = Top
blImp Top f = f; blImp (Tag _ Top) f = f
blImp f g = Imp f g

-- creation of formulas
mkAll, mkExi :: VarName -> Formula -> Formula
mkAll v = bool . All (newDecl v) . bind v
mkExi v = bool . Exi (newDecl v) . bind v

dAll, dExi :: Decl -> Formula -> Formula
dAll dcl = bool . All dcl . bind (declName dcl)
dExi dcl = bool . Exi dcl . bind (declName dcl)


mkVar :: VarName -> Formula
mkVar v = pVar $ PosVar v noSourcePos

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
mkPair :: Formula -> Formula -> Formula
mkPair x y = mkTrm PairId termPair [x,y]
mkObj :: Formula -> Formula
mkObj      = mkTrm ObjectId termObject . pure -- this is a dummy for parsing purposes


-- quick checks of syntactic properties

isVar :: Formula -> Bool
isVar Var{} = True; isVar _ = False
isTrm :: Formula -> Bool
isTrm Trm{} = True; isTrm _ = False

isNotion :: Formula -> Bool
isNotion Trm {trmName = TermNotion _} = True
isNotion _ = False

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