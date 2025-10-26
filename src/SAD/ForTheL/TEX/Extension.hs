-- |
-- Module      : SAD.ForTheL.TEX.Extension
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Language extensions (TeX).


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.TEX.Extension (
  defExtend,
  sigExtend,
  structSigExtend,
  newPredicat,
  newNotion,
  introduceMacro,
  pretypeVariable
) where

import Control.Monad
import Data.Set qualified as Set
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
import SAD.ForTheL.TEX.Pattern qualified as TEX
import SAD.ForTheL.TEX.Statement qualified as TEX
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
    defn = do f <- newPredicat; equiv; g <- TEX.statement; return (f,g)
    equiv = Reports.markupTokenSeqOf Reports.defIff iffPhrases <|> texCommand "iff"

defNotion :: FTL Formula
defNotion = do
  ((n,h),u) <- wellFormedCheck (notionVars . fst) defn; uDecl <- makeDecl u
  return $ dAll uDecl $ Iff (Tag HeadTerm n) h
  where
    defn = do
      (n, u) <- newNotion; isOrEq; (q, f) <- TEX.anotion
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
    sig    = do f <- newPredicat; imp; g <- TEX.statement </> noInfo; return (f,g)
    imp    = token' "is" <|> Reports.markupToken Reports.sigImp "implies" <|> texCommand "implies"
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
      (q, f) <- TEX.anotion -|- noInfo
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
newPredicat = do n <- TEX.newPrdPattern knownVariable; get >>= addExpr n n True

newNotion :: FTL (Formula, PosVar)
newNotion = do
  (n, u) <- TEX.newNotionPattern knownVariable;
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
      f <- TEX.newPrdPattern singleLetterVariable
      Reports.markupTokenSeqOf Reports.macroLet standForPhrases
      g <- TEX.statement
      (_, pos2) <- dot
      return (pos2, (f, g))
    notion = wellFormedCheck (funVars . snd) $ do
      (n, u) <- TEX.unnamedNotion singleLetterVariable
      Reports.markupTokenSeqOf Reports.macroLet standForPhrases
      (q, f) <- TEX.anotion
      (_, pos2) <- dot
      h <- q <$> dig f [pVar u]
      return (pos2, (n, h))

pretypeVariable :: FTL ProofText
pretypeVariable = do
  (pos, tv) <- narrow2 typeVar
  modify $ upd tv
  return $ ProofTextPretyping pos (fst tv)
  where
    typeVar = do
      pos1 <- getPos; Reports.markupToken Reports.synonymLet "let"; vs <- varList; Reports.markupTokenSeqOf Reports.synonymLet standForPhrases
      when (Set.size vs == 0) $ fail "empty variable list in let binding"
      (g, pos2) <- wellFormedCheck (freeOrOverlapping mempty . fst) holedNotion
      let pos = Position.range_position (pos1, pos2)
      Reports.addPretypingReport pos $ map posVarPosition $ Set.toList vs;
      return (pos, (vs, ignoreNames g))

    holedNotion = do
      (q, f) <- TEX.anotion
      g <- q <$> dig f [(mkVar (VarHole ""))]
      (_, pos2) <- dot
      return (g, pos2)

    upd (vs, notion) st = st { tvrExpr = (Set.map posVarName vs, notion) : tvrExpr st }
