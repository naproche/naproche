-- |
-- Module      : SAD.ForTheL.TEX.Base
-- Copyright   : (c) 2025 Marcel Schütz
-- License     : GPL-3
--
-- ForTheL state for FTL-TeX texts.


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.TEX.Base (
  addInits
) where

import Data.List (unionBy)

import SAD.Data.Formula
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
    equalityPredicate = ([Symbol "="], mkTrm EqualityId TermEquality)
    -- "= x"
    equalSymbNotion = ([Symbol "=", Vr], mkTrm EqualityId TermEquality)
    -- "\in X"
    elementOfSymbNotion = ([Symbol "\\in", Vr], \(x:m:_) -> mkElem x m)
    -- "\dom(f)"
    domFunction = ([Symbol "\\dom", Symbol "(",Vr,Symbol ")"], mkDom . head)
    -- "x \neq y"
    inequalityPredicate = ([Symbol "\\neq"], Not . mkTrm EqualityId TermEquality)
    -- "x \prec y"
    inductionPredicate = ([Symbol "\\prec"], mkTrm LessId TermLess)
    -- "x \in X"
    inPredicate = ([Symbol "\\in"], \(x:m:_) -> mkElem x m)
    -- "x \notin X"
    notinPredicate = ([Symbol "\\notin"], \(x:m:_) -> Not $ mkElem x m)

    -- Compare the pattern of two primitive expressions
    comparePatterns p p' = fst p == fst p'