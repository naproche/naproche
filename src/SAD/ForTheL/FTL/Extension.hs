-- |
-- Module      : SAD.ForTheL.FTL.Extension
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Extending the language: definitions, signature extensions, pretypings,
-- macros and synonyms.


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.FTL.Extension (
  defExtend,
  sigExtend,
  structSigExtend
) where

import Control.Applicative

import SAD.Data.Formula
import SAD.ForTheL.Base
import SAD.ForTheL.Extension
import SAD.ForTheL.Statement
import SAD.ForTheL.Reports qualified as Reports
import SAD.Parser.Primitives
import SAD.Parser.Combinators

defExtend :: FTL Formula
defExtend = defPredicat -|- defNotion

sigExtend :: FTL Formula
sigExtend = sigPredicat -|- sigNotion

structSigExtend :: FTL (Formula, Formula)
structSigExtend = sigStructure

defPredicat :: FTL Formula
defPredicat = do
  (f, g) <- wellFormedCheck prdVars defn
  return $ Iff (Tag HeadTerm f) g
  where
    defn = do f <- newPredicat; equiv; g <- statement; return (f,g)
    equiv = Reports.markupTokenSeqOf Reports.defIff iffPhrases <|> symbol "<=>"

defNotion :: FTL Formula
defNotion = do
  ((n,h),u) <- wellFormedCheck (notionVars . fst) defn; uDecl <- makeDecl u
  return $ dAll uDecl $ Iff (Tag HeadTerm n) h
  where
    defn = do
      (n, u) <- newNotion; isOrEq; (q, f) <- anotion
      let v = pVar u; fn = replace v (trm n)
      h <- (fn . q) <$> dig f [v]
      return ((n,h),u)

    isOrEq = token' "=" <|> isEq
    isEq   = token' "is" >> optLL1 () (token' "equal" >> token' "to")
    trm Trm {trmName = TermEquality, trmArgs = [_,t]} = t; trm t = t

sigPredicat :: FTL Formula
sigPredicat = do
  (f,g) <- wellFormedCheck prdVars sig
  return $ Imp (Tag HeadTerm f) g
  where
    sig    = do f <- newPredicat; imp; g <- statement </> noInfo; return (f,g)
    imp    = token' "is" <|> Reports.markupToken Reports.sigImp "implies" <|> symbol "=>"
    noInfo = (tokenSeq' ["an", "atom"] </> tokenSeq' ["a", "relation"]) >> return Top

sigNotion :: FTL Formula
sigNotion = do
  ((n,h),u) <- wellFormedCheck (notionVars . fst) sig
  uDecl <- makeDecl u
  return $ dAll uDecl $ Imp (Tag HeadTerm n) h
  where
    sig = do
      (n, u) <- newNotion
      token' "is"
      (q, f) <- anotion -|- noInfo
      let v = pVar u
      h <- (replace v (trm n) . q) <$> dig f [v]
      return ((n,h),u)

    noInfo =
      (tokenSeq' ["a", "notion"] </> tokenSeq' ["a", "constant"]) >> return (id,Top)
    trm Trm {trmName = TermEquality, trmArgs = [_,t]} = t; trm t = t

sigStructure :: FTL (Formula, Formula)
sigStructure = do
  ((n,h),u) <- wellFormedCheck (notionVars . fst) sig
  uDecl <- makeDecl u
  return (n, dAll uDecl $ Imp (Tag HeadTerm n) h)
  where
    sig = do
      (n, u) <- newNotion
      token' "is"
      token' "a"
      token' "structure"
      let v = pVar u
      h <- replace v (trm n) <$> dig Top [v]
      return ((n,h),u)
    trm Trm {trmName = TermEquality, trmArgs = [_,t]} = t; trm t = t
