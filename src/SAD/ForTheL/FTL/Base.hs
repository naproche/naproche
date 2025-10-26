-- |
-- Module      : SAD.ForTheL.FTL.Base
-- Copyright   : (c) 2025 Marcel Schütz
-- License     : GPL-3
--
-- ForTheL state (FTL).


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.FTL.Base (
  addInits
) where

import Data.List (unionBy)

import SAD.Data.Formula
import SAD.ForTheL.Base


-- | Add primitive expressions to the state.
addInits :: FState -> FState
addInits state@FState{symbNotionExpr = sn, cfnExpr = cfn, iprExpr = ipr} = state {
    symbNotionExpr = unionBy comparePatterns sn [
        equalSymbNotion
      ],
    cfnExpr = unionBy comparePatterns cfn [
        domFunction
      ],
    iprExpr = unionBy comparePatterns ipr [
        equalityPredicate,
        inequalityPredicate,
        inductionPredicate
      ]
  }
  where
    -- "x = y"
    equalityPredicate = ([Symbol "="], mkTrm EqualityId TermEquality)
    -- "= x"
    equalSymbNotion = ([Symbol "=", Vr], mkTrm EqualityId TermEquality)
    -- "x != y"
    inequalityPredicate = ([Symbol "!", Symbol "="], Not . mkTrm EqualityId TermEquality)
    -- "x -<- y"
    inductionPredicate = ([Symbol "-", Symbol "<", Symbol "-"], mkTrm LessId TermLess)
    -- "Dom f"
    domFunction = ([Symbol "Dom", Vr], mkDom . head)

    -- Compare the pattern of two primitive expressions
    comparePatterns p p' = fst p == fst p'