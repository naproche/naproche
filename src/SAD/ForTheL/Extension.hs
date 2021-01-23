{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Extending the language: definitions, signature extensions, pretypings,
macros and synonyms.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Extension (
  pretypeVariable,
  introduceMacro,
  defExtend,
  sigExtend)
  where


import SAD.Core.SourcePos
import SAD.Data.Formula
import SAD.Data.Text.Block (ProofText (..))

import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Pattern
import SAD.ForTheL.Reports
import SAD.Parser.Primitives
import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Data.Text.Decl

import Control.Monad
import qualified Data.Set as Set
import Control.Applicative
import Control.Monad.State.Class (get, modify)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

-- definitions and signature extensions

defExtend :: FTL Formula
defExtend = defPredicat -|- defNotion
sigExtend :: FTL Formula
sigExtend = sigPredicat -|- sigNotion

defPredicat :: FTL Formula
defPredicat = do
  (f, g) <- wellFormedCheck prdVars defn
  return $ Iff (Tag HeadTerm f) g
  where
    defn = do f <- newPredicat; equiv; g <- statement; return (f,g)
    equiv = iff <|> symbol "<=>"

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
    isEq   = is >> optLL1 () (token' "equal" >> token' "to")
    trm Trm {trmName = TermEquality, trmArgs = [_,t]} = t; trm t = t



sigPredicat :: FTL Formula
sigPredicat = do
  (f,g) <- wellFormedCheck prdVars sig
  return $ Imp (Tag HeadTerm f) g
  where
    sig    = do f <- newPredicat; imp; g <- statement </> noInfo; return (f,g)
    imp    = token' "is" <|> token' "implies" <|> symbol "=>"
    noInfo = art >> tokenOf' ["atom", "relation"] >> return Top


sigNotion :: FTL Formula
sigNotion = do
  ((n,h),u) <- wellFormedCheck (notionVars . fst) sig
  uDecl <- makeDecl u
  return $ dAll uDecl $ Imp (Tag HeadTerm n) h
  where
    sig = do
      (n, u) <- newNotion
      is
      (q, f) <- anotion -|- noInfo
      let v = pVar u
      h <- (replace v (trm n) . q) <$> dig f [v]
      return ((n,h),u)

    noInfo =
      art >> tokenOf' ["notion", "constant"] >> return (id,Top)
    trm Trm {trmName = TermEquality, trmArgs = [_,t]} = t; trm t = t

newPredicat :: FTL Formula
newPredicat = do n <- newPrdPattern knownVariable; get >>= addExpr n n True

newNotion :: FTL (Formula, PosVar)
newNotion = do
  (n, u) <- newNotionPattern knownVariable;
  f <- get >>= addExpr n n True
  return (f, u)

-- well-formedness check

funVars, notionVars, prdVars :: (Formula, Formula) -> Maybe Text

funVars (f, d) | not ifq   = prdVars (f, d)
               | not idq   = Just $ Text.pack $ "illegal function alias: " ++ show d
               | otherwise = prdVars (t {trmArgs = v:trmArgs t}, d)
  where
    ifq = isTrm f && trmName f == TermEquality && isTrm t
    idq = isTrm d && trmName d == TermEquality && not (u `occursIn` p)
    Trm {trmName = TermEquality, trmArgs = [v, t]} = f
    Trm {trmName = TermEquality, trmArgs = [u, p]} = d


notionVars (f, d) | not isFunction = prdVars (f, d)
               | otherwise      = prdVars (t {trmArgs = v:vs}, d)
  where
    isFunction = isTrm f && trmName f == TermEquality && isTrm t
    Trm {trmName = TermEquality, trmArgs =  [v,t]} = f
    Trm {trmArgs = vs} = t


prdVars (f, d) | not flat  = Just $ Text.pack $ "compound expression: " ++ show f
               | otherwise = freeOrOverlapping (fvToVarSet $ free f) d
  where
    flat      = isTrm f && allDistinctVars (trmArgs f)


allDistinctVars :: [Formula] -> Bool
allDistinctVars = disVs []
  where
    disVs ls (Var {varName = v@(VarHidden _)} : vs) = notElem v ls && disVs (v:ls) vs
    disVs ls (Var {varName = v@(VarConstant _)} : vs) = notElem v ls && disVs (v:ls) vs
    disVs _ [] = True
    disVs _ _ = False



pretypeVariable :: FTL ProofText
pretypeVariable = do
  (pos, tv) <- narrow typeVar
  modify $ upd tv
  return $ ProofTextPretyping pos (fst tv)
  where
    typeVar = do
      pos1 <- getPos; markupToken synonymLet "let"; vs <- varList; standFor
      when (Set.size vs == 0) $ fail "empty variable list in let binding"
      (g, pos2) <- wellFormedCheck (freeOrOverlapping mempty . fst) holedNotion
      let pos = rangePos $ SourceRange pos1 pos2
      addPretypingReport pos $ map posVarPosition $ Set.toList vs;
      return (pos, (vs, ignoreNames g))

    holedNotion = do
      (q, f) <- anotion
      g <- q <$> dig f [(mkVar (VarHole ""))]
      SourceRange _ pos2 <- dot
      return (g, pos2)

    upd (vs, notion) st = st { tvrExpr = (Set.map posVarName vs, notion) : tvrExpr st }


introduceMacro :: FTL ProofText
introduceMacro = do
  pos1 <- getPos
  markupToken macroLet "let"
  (pos2, (f, g)) <- narrow (prd -|- notion)
  let pos = rangePos $ SourceRange pos1 pos2
  addMacroReport pos
  st <- get
  addExpr f (ignoreNames g) False st
  return $ ProofTextMacro pos
  where
    prd, notion :: FTL (SourcePos, (Formula, Formula))
    prd = wellFormedCheck (prdVars . snd) $ do
      f <- newPrdPattern singleLetterVariable
      standFor
      g <- statement
      SourceRange _ pos2 <- dot
      return (pos2, (f, g))
    notion = wellFormedCheck (funVars . snd) $ do
      (n, u) <- unnamedNotion singleLetterVariable
      standFor
      (q, f) <- anotion
      SourceRange _ pos2 <- dot
      h <- q <$> dig f [pVar u]
      return (pos2, (n, h))

ignoreNames :: Formula -> Formula
ignoreNames (All dcl f) = All dcl {declName = VarEmpty} $ ignoreNames f
ignoreNames (Exi dcl f) = Exi dcl {declName = VarEmpty} $ ignoreNames f
ignoreNames f@Trm{}   = f
ignoreNames f         = mapF ignoreNames f
