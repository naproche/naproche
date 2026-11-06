{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.ForTheL.TEX.Pattern
-- Description : Pattern parsing (TeX).
-- Copyright   : (c) 2025, Marcel Schütz
-- License     : GPL-3
module SAD.ForTheL.TEX.Pattern (
  newPredicate,
  newNamedNotion,
  newUnnamedNotion,
) where

import Control.Applicative
import Control.Monad

import SAD.Data.Formula
import SAD.ForTheL.Base
import SAD.ForTheL.Pattern
import SAD.Parser.Combinators
import SAD.Parser.Primitives


-- New patterns


newPredicate :: FTL PosVar -> FTL Formula
newPredicate tvr = multi </> unary </> optInTexArg "emph" (newSymbol tvr)
  where
    unary = do
      v <- tvr
      (t, vs) <- unaryAdj -|- unaryVerb
      return $ mkTrm NewId t $ map pVar (v:vs)
    multi = do
      (u,v) <- liftM2 (,) tvr (tokenOf' [",", "and"] >> tvr)
      (t, vs) <- multiAdj -|- multiVerb
      return $ mkTrm NewId t $ map pVar (u:v:vs)

    unaryAdj = do
      token' "is"
      (t, vs) <- optInTexArg "emph" $ predicatePattern tvr
      return (TermUnaryAdjective t, vs)
    multiAdj = do
      token' "are"
      (t, vs) <- optInTexArg "emph" $ predicatePattern tvr
      return (TermMultiAdjective t, vs)
    unaryVerb = do
      (t, vs) <- optInTexArg "emph" $ predicatePattern tvr
      return (TermUnaryVerb t, vs)
    multiVerb = do
      (t, vs) <- optInTexArg "emph" $ predicatePattern tvr
      return (TermMultiVerb t, vs)

newNamedNotion :: FTL PosVar -> FTL (Formula, PosVar)
newNamedNotion tvr = (notion <|> function) </> newUnnamedNotion tvr
  where
    notion = do
      tokenOf' ["a", "an"]
      (t, v:vs) <- optInTexArg "emph" $ namedNotionPattern tvr
      return (mkTrm NewId (TermNotion t) $ map pVar (v:vs), v)
    function = do
      token' "the"
      (t, v:vs) <- optInTexArg "emph" $ namedNotionPattern tvr
      return (mkEquality (pVar v) $ mkTrm NewId (TermNotion t) $ map pVar vs, v)

newUnnamedNotion :: FTL PosVar -> FTL (Formula, PosVar)
newUnnamedNotion tvr = (notion <|> function) </> (optInTexArg "emph" (newSymbol tvr) >>= equ)
  where
    notion = do
      tokenOf' ["a", "an"]
      (t, v:vs) <- optInTexArg "emph" $ unnamedNotionPattern tvr
      return (mkTrm NewId (TermNotion t) $ map pVar (v:vs), v)
    function = do
      token' "the"
      (t, v:vs) <- optInTexArg "emph" $ unnamedNotionPattern tvr
      return (mkEquality (pVar v) $ mkTrm NewId (TermNotion t) $ map pVar vs, v)
    equ t = do
      v <- hidden
      return (mkEquality (pVar v) t, v)


newSymbol :: FTL PosVar -> FTL Formula
newSymbol tvr = left -|- right
  where
    left = do
      (t, vs) <- symbolPatternHead tvr
      return $ mkTrm NewId (TermSymbolic t) $ map pVar vs
    right = do
      (t, vs) <- symbolPatternTail tvr
      guard $ not $ null $ tail t
      return $ mkTrm NewId (TermSymbolic t) $ map pVar vs
