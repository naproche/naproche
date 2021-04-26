{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Various functions on formulas.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Formula.Kit 
  ( blImp, blAnd
  , free, pVar, occursH, occursS, allFree, duplicateNames, dExi, dAll
  , mkTrm, mkEquality, mkAll, mkVar, mkExi, mkThesis
  , isNotion, isTrm, isVar, mkClass, mkObject, mkSet, mkElem, isClass
  ) where

import SAD.Data.Formula.Base
import SAD.Core.SourcePos
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

-- | Given a variable name with position data, creates a formula consisting of just
-- a that variable.
pVar :: PosVar -> Formula
pVar (PosVar v pos) = Var v [] pos

mkTrm :: TermId -> TermName -> [Formula] -> Formula
mkTrm tId t ts = Trm t ts [] (AllEq tId)


-- creation of predefined functions and notions

mkEquality :: Formula -> Formula -> Formula
mkEquality t s  = mkTrm EqualityId TermEquality [t,s]
mkThesis :: Formula
mkThesis   = mkTrm ThesisId TermThesis []
mkSet :: Formula -> Formula
mkSet      = mkTrm SetId termSet . pure
mkClass :: Formula -> Formula
mkClass      = mkTrm ClassId termClass . pure
mkObject :: Formula -> Formula
mkObject      = mkTrm ObjectId termObject . pure -- this is a dummy for parsing purposes
mkElem :: Formula -> Formula -> Formula
mkElem x m = mkTrm ElementId termElement [x,m]

-- quick checks of syntactic properties

isVar :: Formula -> Bool
isVar Var{} = True; isVar _ = False
isTrm :: Formula -> Bool
isTrm Trm{} = True; isTrm _ = False
isClass :: Formula -> Bool
isClass (Class _ _) = True;
isClass (FinClass _) = True;
isClass (InClass _ _ _) = True;
isClass _ = False

isNotion :: Formula -> Bool
isNotion Trm {trmName = TermNotion _} = True
isNotion _ = False

-- Holes and slots

occursH, occursS :: Formula -> Bool
occursH = ((mkVar (VarHole "")) `occursIn`)
occursS = ((mkVar VarSlot) `occursIn`)

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