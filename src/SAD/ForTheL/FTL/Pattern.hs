{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.ForTheL.FTL.Pattern
-- Description : Pattern parsing (FTL).
-- Copyright   : (c) 2025, Marcel Schütz
-- License     : GPL-3
module SAD.ForTheL.FTL.Pattern (
  newPrdPattern,
  unnamedNotion,
  newNotionPattern
) where

import Control.Applicative
import Control.Monad

import SAD.Data.Formula
import SAD.ForTheL.Base
import SAD.ForTheL.Pattern
import SAD.Parser.Combinators
import SAD.Parser.Primitives


-- New patterns


newPrdPattern :: FTL PosVar -> FTL Formula
newPrdPattern tvr = multi </> unary </> newSymbPattern tvr
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
      (t, vs) <- wordPatHead tvr
      return (TermUnaryAdjective t, vs)
    multiAdj = do
      token' "are"
      (t, vs) <- wordPatHead tvr
      return (TermMultiAdjective t, vs)
    unaryVerb = do
      (t, vs) <- wordPatHead tvr
      return (TermUnaryVerb t, vs)
    multiVerb = do
      (t, vs) <- wordPatHead tvr
      return (TermMultiVerb t, vs)

newNotionPattern :: FTL PosVar -> FTL (Formula, PosVar)
newNotionPattern tvr = (notion <|> function) </> unnamedNotion tvr
  where
    notion = do
      tokenOf' ["a", "an"]
      (t, v:vs) <- patName tvr
      return (mkTrm NewId (TermNotion t) $ map pVar (v:vs), v)
    function = do
      token' "the"
      (t, v:vs) <- patName tvr
      return (mkEquality (pVar v) $ mkTrm NewId (TermNotion t) $ map pVar vs, v)

unnamedNotion :: FTL PosVar -> FTL (Formula, PosVar)
unnamedNotion tvr = (notion <|> function) </> (newSymbPattern tvr >>= equ)
  where
    notion = do
      tokenOf' ["a", "an"]
      (t, v:vs) <- patNoName tvr
      return (mkTrm NewId (TermNotion t) $ map pVar (v:vs), v)
    function = do
      token' "the"
      (t, v:vs) <- patNoName tvr
      return (mkEquality (pVar v) $ mkTrm NewId (TermNotion t) $ map pVar vs, v)
    equ t = do
      v <- hidden
      return (mkEquality (pVar v) t, v)


newSymbPattern :: FTL PosVar -> FTL Formula
newSymbPattern tvr = left -|- right
  where
    left = do
      (t, vs) <- symbPatHead tvr
      return $ mkTrm NewId (TermSymbolic t) $ map pVar vs
    right = do
      (t, vs) <- symbPatTail tvr
      guard $ not $ null $ tail t
      return $ mkTrm NewId (TermSymbolic t) $ map pVar vs
