{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Extending the language: definitions, signature extensions, pretypings,
macros and synonyms.
-}



module SAD.ForTheL.Extension (
  pretypeVariable,
  introduceMacro,
  defExtend,
  sigExtend)
  where


import SAD.Core.SourcePos
import SAD.Data.Formula
import SAD.Data.Text.Block (Text (..))

import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Pattern
import SAD.ForTheL.Reports
import SAD.Parser.Primitives
import SAD.Parser.Base
import SAD.Parser.Combinators
import qualified SAD.Data.Text.Decl as Decl
import SAD.Core.SourcePos (SourceRange(..))


import Control.Applicative
import qualified Control.Monad.State.Class as MS



-- for tests
import SAD.Parser.Token
import Debug.Trace


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
  ((n,h),u) <- wellFormedCheck (ntnVars . fst) defn; uDecl <- makeDecl u
  return $ dAll uDecl $ Iff (Tag HeadTerm n) h
  where
    defn = do
      (n, u) <- newNotion; isOrEq; (q, f) <- anotion
      let v = pVar u; fn = replace v (trm n)
      h <- (fn . q) <$> dig f [v]
      return ((n,h),u)

    isOrEq = wdToken "=" <|> isEq
    isEq   = is >> optLL1 () (wdToken "equal" >> wdToken "to")
    trm Trm {trName = "=", trArgs = [_,t]} = t; trm t = t



sigPredicat :: FTL Formula
sigPredicat = do
  (f,g) <- wellFormedCheck prdVars sig
  return $ Imp (Tag HeadTerm f) g
  where
    sig    = do f <- newPredicat; imp; g <- statement </> noInfo; return (f,g)
    imp    = wdToken "is" <|> wdToken "implies" <|> symbol "=>"
    noInfo = art >> wdTokenOf ["atom", "relation"] >> return Top


sigNotion :: FTL Formula
sigNotion = do
  ((n,h),u) <- wellFormedCheck (ntnVars . fst) sig; uDecl <- makeDecl u
  return $ dAll uDecl $ Imp (Tag HeadTerm n) h
  where
    sig = do
      (n, u) <- newNotion; is; (q, f) <- anotion -|- noInfo
      let v = pVar u; fn = replace v (trm n)
      h <- fmap (fn . q) $ dig f [v]
      return ((n,h),u)

    noInfo =
      art >> wdTokenOf ["notion", "constant"] >> return (id,Top)
    trm Trm {trName = "=", trArgs = [_,t]} = t; trm t = t

newPredicat :: FTL Formula
newPredicat = do n <- newPrdPattern nvr; MS.get >>= addExpr n n True

newNotion :: FTL (Formula, (String, SourcePos))
newNotion = do
  (n, u) <- newNtnPattern nvr;
  f <- MS.get >>= addExpr n n True
  return (f, u)

-- well-formedness check

funVars, ntnVars, prdVars :: (Formula, Formula) -> Maybe String

funVars (f, d) | not ifq   = prdVars (f, d)
               | not idq   = Just $ "illegal function alias: " ++ show d
               | otherwise = prdVars (t {trArgs = v:trArgs t}, d)
  where
    ifq = isEquality f && isTrm t
    idq = isEquality d && not (occurs u p)
    Trm {trName = "=", trArgs = [v, t]} = f
    Trm {trName = "=", trArgs = [u, p]} = d


ntnVars (f, d) | not isFunction = prdVars (f, d)
               | otherwise      = prdVars (t {trArgs = v:vs}, d)
  where
    isFunction = isEquality f && isTrm t
    Trm {trName = "=", trArgs =  [v,t]} = f
    Trm {trArgs = vs} = t


prdVars (f, d) | not flat  = return $ "compound expression: " ++ show f
               | otherwise = overfree (free [] f) d
  where
    flat      = isTrm f && allDistinctVars (trArgs f)


allDistinctVars :: [Formula] -> Bool
allDistinctVars = disVs []
  where
    disVs ls (Var {trName = v@('h':_)} : vs) = notElem v ls && disVs (v:ls) vs
    disVs ls (Var {trName = v@('x':_)} : vs) = notElem v ls && disVs (v:ls) vs
    disVs _ [] = True
    disVs _ _ = False



--- introduce synonyms


nonLogicalLanguageExt :: FTL Text
nonLogicalLanguageExt = pretypeVariable </> introduceMacro


pretypeVariable :: FTL Text
pretypeVariable = do
  (pos, tv) <- narrow typeVar
  MS.modify $ upd tv
  return $ TextPretyping pos (fst tv)
  where
    typeVar = do
      pos1 <- getPos; markupToken synonymLet "let"; vs@(_:_) <- varlist; standFor;
      (g, pos2) <- wellFormedCheck (overfree [] . fst) holedNotion
      let pos = rangePos $ SourceRange pos1 pos2
      addPretypingReport pos $ map snd vs;
      return (pos, (vs, ignoreNames g))

    holedNotion = do
      (q, f) <- anotion
      g <- q <$> dig f [zHole]
      SourceRange _ pos2 <- dot
      return (g, pos2)

    upd (vs, ntn) st = st { tvrExpr = (map fst vs, ntn) : tvrExpr st }


introduceMacro :: FTL Text
introduceMacro = do
  pos1 <- getPos; markupToken macroLet "let"
  (pos2, (f, g)) <- narrow (prd -|- ntn)
  let pos = rangePos $ SourceRange pos1 pos2
  addMacroReport pos
  MS.get >>= addExpr f (ignoreNames g) False
  return $ TextMacro pos
  where
    prd = wellFormedCheck (prdVars . snd) $ do
      f <- newPrdPattern avr
      standFor; g <- statement; SourceRange _ pos2 <- dot; return (pos2, (f, g))
    ntn = wellFormedCheck (funVars . snd) $ do
      (n, u) <- unnamedNotion avr
      standFor; (q, f) <- anotion; SourceRange _ pos2 <- dot
      h <- fmap q $ dig f [pVar u]; return (pos2, (n, h))

ignoreNames :: Formula -> Formula
ignoreNames (All dcl f) = All dcl {Decl.name = ""} $ ignoreNames f
ignoreNames (Exi dcl f) = Exi dcl {Decl.name = ""} $ ignoreNames f
ignoreNames f@Trm{}   = f
ignoreNames f         = mapF ignoreNames f
