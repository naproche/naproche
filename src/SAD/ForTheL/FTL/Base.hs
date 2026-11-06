{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.ForTheL.FTL.Base
-- Description : ForTheL state (FTL).
-- Copyright   : (c) 2025, Marcel Schütz
-- License     : GPL-3
module SAD.ForTheL.FTL.Base (
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
    equalityPredicate = ([SymbSymbol "="], mkTrm EqualityId TermEquality)
    -- "= x"
    equalSymbNotion = ([SymbSymbol "=", SymbVar], mkTrm EqualityId TermEquality)
    -- "x != y"
    inequalityPredicate = ([SymbSymbol "!", SymbSymbol "="], Not . mkTrm EqualityId TermEquality)
    -- "x -<- y"
    inductionPredicate = ([SymbSymbol "-", SymbSymbol "<", SymbSymbol "-"], mkTrm LessId TermLess)
    -- "Dom f"
    domFunction = ([SymbSymbol "Dom", SymbVar], mkDom . head)

    -- Compare the pattern of two primitive expressions
    comparePatterns p p' = fst p == fst p'
