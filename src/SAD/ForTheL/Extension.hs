{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Extending the language: definitions, signature extensions, pretypings,
macros and synonyms.
-}



module SAD.ForTheL.Extension (
  introduceSynonym,
  pretypeVariable,
  introduceMacro,
  defExtend,
  sigExtend)
  where


import SAD.Core.SourcePos
import SAD.Data.Formula
import qualified SAD.Data.Instr as Instr
import SAD.Data.Text.Block (Block, Text (..))

import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Pattern
import SAD.ForTheL.Instruction (instrPos)
import SAD.Parser.Primitives
import SAD.Parser.Base
import SAD.Parser.Combinators
import qualified SAD.Data.Text.Decl as Decl


import Control.Monad
import Data.Maybe (isNothing, fromJust)
import qualified Control.Monad.State.Class as MS



-- for tests
import SAD.Parser.Token
import Debug.Trace


-- definitions and signature extensions

defExtend = defPredicat -|- defNotion
sigExtend = sigPredicat -|- sigNotion

defPredicat = do
  (f, g) <- wellFormedCheck prdVars defn
  return $ Iff (Tag HeadTerm f) g
  where
    defn = do f <- newPredicat; equiv; g <- statement; return (f,g)
    equiv = iff <|> symbol "<=>"

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



sigPredicat = do
  (f,g) <- wellFormedCheck prdVars sig
  return $ Imp (Tag HeadTerm f) g
  where
    sig    = do f <- newPredicat; imp; g <- statement </> noInfo; return (f,g)
    imp    = wdToken "is" <|> wdToken "implies" <|> symbol "=>"
    noInfo = art >> wdTokenOf ["atom", "relation"] >> return Top


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
      art >> wdTokenOf ["notion", "function", "constant"] >> return (id,Top)
    trm Trm {trName = "=", trArgs = [_,t]} = t; trm t = t

newPredicat = do n <- newPrdPattern nvr; MS.get >>= addExpr n n True

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


allDistinctVars = disVs []
  where
    disVs ls (Var {trName = v@('h':_)} : vs) = notElem v ls && disVs (v:ls) vs
    disVs ls (Var {trName = v@('x':_)} : vs) = notElem v ls && disVs (v:ls) vs
    disVs _ [] = True
    disVs _ _ = False



--- introduce synonyms


nonLogicalLanguageExt :: Parser FState Text
nonLogicalLanguageExt = introduceSynonym </> pretypeVariable </> introduceMacro

introduceSynonym :: Parser FState Text
introduceSynonym = do
  (pos, ss) <- sym
  MS.modify $ upd ss
  return $ TextSynonym $ Instr.position pos
  where
    upd ss st = st { strSyms = ss : strSyms st }

    sym = instrPos $ do
      w <- word ; root <- optLL1 w $ sfx w; smTokenOf "/"
      syms <- (wlexem -|- sfx w) `sepByLL1` smTokenOf "/"
      return $ root : syms
    sfx w = smTokenOf "-" >> fmap (w ++) word


pretypeVariable :: Parser FState Text
pretypeVariable = do
  (pos, tv) <- narrow typeVar
  MS.modify $ upd tv
  return $ TextPretyping pos
  where
    typeVar = do
      pos <- wdTokenPos "let"; vs@(_:_) <- varlist; standFor;
      g <- wellFormedCheck (overfree []) (finish holedNotion)
      return (pos, (map fst vs, ignoreNames g))

    holedNotion = do (q, f) <- anotion; q <$> dig f [zHole]

    upd tv st = st { tvrExpr = tv : tvrExpr st }


introduceMacro :: Parser FState Text
introduceMacro = do
  pos <- wdTokenPos "let"
  (f, g) <- narrow (prd -|- ntn)
  MS.get >>= addExpr f (ignoreNames g) False
  return $ TextMacro pos
  where
    prd = wellFormedCheck prdVars $ do
      f <- newPrdPattern avr
      g <- standFor >> finish statement; return (f, g)
    ntn = wellFormedCheck funVars $ do
      (n, u) <- unnamedNotion avr
      (q, f) <- standFor >> finish anotion
      h <- fmap q $ dig f [pVar u]; return (n, h)

ignoreNames (All dcl f) = All dcl {Decl.name = ""} $ ignoreNames f
ignoreNames (Exi dcl f) = Exi dcl {Decl.name = ""} $ ignoreNames f
ignoreNames f@Trm{}   = f
ignoreNames f         = mapF ignoreNames f
