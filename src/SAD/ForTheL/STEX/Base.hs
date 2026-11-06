{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.ForTheL.STEX.Base
-- Description : ForTheL state (sTeX).
-- Copyright   : (c) 2025, Marcel Schütz
-- License     : GPL-3
module SAD.ForTheL.STEX.Base (
  addInits
) where

import Data.List (unionBy)

import SAD.Data.Formula
import SAD.Data.Pattern
import SAD.ForTheL.Base


-- | Add primitive expressions to the state.
addInits :: FState -> FState
addInits state@FState{symbNotionExpr = sn, cfnExpr = cfn, iprExpr = ipr} = state {
    symbNotionExpr = unionBy comparePatterns sn [
        equalSymbNotion,
        elementOfSymbNotion
      ],
    cfnExpr = unionBy comparePatterns cfn [
        domFunction
      ],
    iprExpr = unionBy comparePatterns ipr [
        equalityPredicate,
        inequalityPredicate,
        inductionPredicate,
        inPredicate,
        notinPredicate
      ]
  }
  where
    -- "\Elem x"
    elementOfSymbNotion = ([SymbSymbol "\\Elem", SymbVar], \(x:m:_) -> mkElem x m)
    -- "\Eq x"
    equalSymbNotion = ([SymbSymbol "\\Eq", SymbVar], mkTrm EqualityId TermEquality)
    -- "\Dom(f)"
    domFunction = ([SymbSymbol "\\Dom", SymbSymbol "(", SymbVar, SymbSymbol ")"], mkDom . head)
    -- "x \Eq y"
    equalityPredicate = ([SymbSymbol "\\Eq"], mkTrm EqualityId TermEquality)
    -- "x \NotEq y"
    inequalityPredicate = ([SymbSymbol "\\NotEq"], Not . mkTrm EqualityId TermEquality)
    -- "x \ILess y"
    inductionPredicate = ([SymbSymbol "\\ILess"], mkTrm LessId TermLess)
    -- "x \Elem y"
    inPredicate = ([SymbSymbol "\\Elem"], \(x:m:_) -> mkElem x m)
    -- "x \NotElem y"
    notinPredicate = ([SymbSymbol "\\NotElem"], \(x:m:_) -> Not $ mkElem x m)

    -- Compare the pattern of two primitive expressions
    comparePatterns p p' = fst p == fst p'
