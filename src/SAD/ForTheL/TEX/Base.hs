{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.ForTheL.TEX.Base
-- Description : ForTheL state (TeX).
-- Copyright   : (c) 2025, Marcel Schütz
-- License     : GPL-3
module SAD.ForTheL.TEX.Base (
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
    -- "x = y"
    equalityPredicate = ([SymbSymbol "="], mkTrm EqualityId TermEquality)
    -- "= x"
    equalSymbNotion = ([SymbSymbol "=", SymbVar], mkTrm EqualityId TermEquality)
    -- "\in X"
    elementOfSymbNotion = ([SymbSymbol "\\in", SymbVar], \(x:m:_) -> mkElem x m)
    -- "\dom(f)"
    domFunction = ([SymbSymbol "\\dom", SymbSymbol "(", SymbVar, SymbSymbol ")"], mkDom . head)
    -- "x \neq y"
    inequalityPredicate = ([SymbSymbol "\\neq"], Not . mkTrm EqualityId TermEquality)
    -- "x \prec y"
    inductionPredicate = ([SymbSymbol "\\prec"], mkTrm LessId TermLess)
    -- "x \in X"
    inPredicate = ([SymbSymbol "\\in"], \(x:m:_) -> mkElem x m)
    -- "x \notin X"
    notinPredicate = ([SymbSymbol "\\notin"], \(x:m:_) -> Not $ mkElem x m)

    -- Compare the pattern of two primitive expressions
    comparePatterns p p' = fst p == fst p'
