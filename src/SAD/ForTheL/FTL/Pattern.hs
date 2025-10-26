-- |
-- Module      : SAD.ForTheL.FTL.Pattern
-- Copyright   : (c) 2025 Marcel Schütz
-- License     : GPL-3
--
-- Pattern parsing (FTL).


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.FTL.Pattern (
  newPrdPattern,
  unnamedNotion,
  newNotionPattern
) where

import Control.Applicative
import Control.Monad
import Data.Text.Lazy qualified as Text

import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.ForTheL.Base
import SAD.ForTheL.Pattern
import SAD.Data.Formula


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
      (t, vs) <- patHead unknownAlpha tvr
      return (TermUnaryAdjective t, vs)
    multiAdj = do
      token' "are"
      (t, vs) <- patHead unknownAlpha tvr
      return (TermMultiAdjective t, vs)
    unaryVerb = do
      (t, vs) <- patHead unknownAlpha tvr
      return (TermUnaryVerb t, vs)
    multiVerb = do
      (t, vs) <- patHead unknownAlpha tvr
      return (TermMultiVerb t, vs)

newNotionPattern :: FTL PosVar -> FTL (Formula, PosVar)
newNotionPattern tvr = (notion <|> function) </> unnamedNotion tvr
  where
    notion = do
      tokenOf' ["a", "an"]
      (t, v:vs) <- patName unknownAlpha tvr
      return (mkTrm NewId (TermNotion t) $ map pVar (v:vs), v)
    function = do
      token' "the"
      (t, v:vs) <- patName unknownAlpha tvr
      return (mkEquality (pVar v) $ mkTrm NewId (TermNotion t) $ map pVar vs, v)

unnamedNotion :: FTL PosVar -> FTL (Formula, PosVar)
unnamedNotion tvr = (notion <|> function) </> (newSymbPattern tvr >>= equ)
  where
    notion = do
      tokenOf' ["a", "an"]
      (t, v:vs) <- patNoName unknownAlpha tvr
      return (mkTrm NewId (TermNotion t) $ map pVar (v:vs), v)
    function = do
      token' "the"
      (t, v:vs) <- patNoName unknownAlpha tvr
      return (mkEquality (pVar v) $ mkTrm NewId (TermNotion t) $ map pVar vs, v)
    equ t = do
      v <- hidden
      return (mkEquality (pVar v) t, v)


newSymbPattern :: FTL PosVar -> FTL Formula
newSymbPattern tvr = left -|- right
  where
    left = do
      (t, vs) <- patHead slexem tvr
      return $ mkTrm NewId (TermName t) $ map pVar vs
    right = do
      (t, vs) <- patTail slexem tvr
      guard $ not $ null $ tail $ Text.words t
      return $ mkTrm NewId (TermName t) $ map pVar vs
