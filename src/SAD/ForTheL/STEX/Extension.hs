-- |
-- Module      : SAD.ForTheL.STEX.Extension
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Language extensions (sTeX).


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.STEX.Extension (
  defExtend,
  sigExtend,
  structSigExtend,
  newPredicat,
  newNotion,
  introduceMacro
) where

import Control.Applicative
import Control.Monad.State.Class

import SAD.Data.Formula
import SAD.Data.Text.Block (ProofText (..))
import SAD.ForTheL.Base
import SAD.ForTheL.Extension
import SAD.ForTheL.Statement
import SAD.ForTheL.Reports qualified as Reports
import SAD.Parser.Base
import SAD.ForTheL.Pattern
import SAD.ForTheL.STEX.Pattern qualified as STEX
import SAD.Parser.Primitives
import SAD.Parser.Combinators

import Isabelle.Position qualified as Position


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
    equiv = Reports.markupTokenSeqOf Reports.defIff iffPhrases <|> texCommand "Iff"

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

    isOrEq = texCommand "DefEq" <|> isEq
    isEq   = token' "is" >> optLL1 () (token' "equal" >> token' "to")
    trm Trm {trmName = TermEquality, trmArgs = [_,t]} = t; trm t = t

sigPredicat :: FTL Formula
sigPredicat = do
  (f,g) <- wellFormedCheck prdVars sig
  return $ Imp (Tag HeadTerm f) g
  where
    sig    = do f <- newPredicat; imp; g <- statement </> noInfo; return (f,g)
    imp    = token' "is" <|> Reports.markupToken Reports.sigImp "implies" <|> texCommand "Implies"
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

newPredicat :: FTL Formula
newPredicat = do n <- STEX.newPrdPattern knownVariable; get >>= addExpr n n True

newNotion :: FTL (Formula, PosVar)
newNotion = do
  (n, u) <- STEX.newNotionPattern knownVariable;
  f <- get >>= addExpr n n True
  return (f, u)

introduceMacro :: FTL ProofText
introduceMacro = do
  pos1 <- getPos
  Reports.markupToken Reports.macroLet "let"
  (pos2, (f, g)) <- narrow2 (prd -|- notion)
  let pos = Position.range_position (pos1, pos2)
  Reports.addMacroReport pos
  st <- get
  addExpr f (ignoreNames g) False st
  return $ ProofTextMacro pos
  where
    prd, notion :: FTL (Position.T, (Formula, Formula))
    prd = wellFormedCheck (prdVars . snd) $ do
      f <- STEX.newPrdPattern singleLetterVariable
      Reports.markupTokenSeqOf Reports.macroLet standForPhrases
      g <- statement
      (_, pos2) <- dot
      return (pos2, (f, g))
    notion = wellFormedCheck (funVars . snd) $ do
      (n, u) <- STEX.unnamedNotion singleLetterVariable
      Reports.markupTokenSeqOf Reports.macroLet standForPhrases
      (q, f) <- anotion
      (_, pos2) <- dot
      h <- q <$> dig f [pVar u]
      return (pos2, (n, h))
