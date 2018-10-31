{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Extending the language: definitions, signature extensions, pretypings,
macros and synonyms.
-}



module Alice.ForTheL.Extension (introduceSynonym, pretypeVariable, introduceMacro, defExtend, sigExtend) where


import Alice.Data.Formula

import Alice.ForTheL.Base
import Alice.ForTheL.Statement
import Alice.ForTheL.Pattern
import Alice.Parser.Primitives

import Alice.Parser.Base
import Alice.Parser.Combinators


import Control.Monad
import Data.Maybe (isNothing, fromJust)
import qualified Control.Monad.State.Class as MS



-- for tests
import Alice.Parser.Token
import Debug.Trace


-- definitions and signature extensions

defExtend = def_predicat -|- def_notion
sigExtend = sig_predicat -|- sig_notion

def_predicat = do
  (f, g) <- wellFormedCheck prdVars defn
  return $ Iff (Tag HeadTerm f) g
  where
    defn  = do f <- new_predicat; equiv; g <- statement; return (f,g)
    equiv = iff <|> symbol "<=>"

def_notion = do
  ((n,h),u) <- wellFormedCheck (ntnVars . fst) defn
  return $ zAll u $ Iff (Tag HeadTerm n) h
  where
    defn = do
      (n, u) <- new_notion; isOrEq; (q, f) <- anotion
      let v = zVar u; fn = replace v (trm n)
      h <- liftM (fn . q) $ dig f [v]
      return ((n,h),u)

    isOrEq = wd_token "=" <|> isEq
    isEq   = is >> optLL1 () (wd_token "equal" >> wd_token "to")
    trm Trm {trName = "=", trArgs = [_,t]} = t; trm t = t



sig_predicat = do
  (f,g) <- wellFormedCheck prdVars sig
  return $ Imp (Tag HeadTerm f) g
  where
    sig    = do f <- new_predicat; imp; g <- statement </> noInfo; return (f,g)
    imp    = wd_token "is" <|> wd_token "implies" <|> symbol "=>"
    noInfo = art >> wd_tokenOf ["atom", "relation"] >> return Top


sig_notion = do
  ((n,h),u) <- wellFormedCheck (ntnVars . fst) sig
  return $ zAll u $ Imp (Tag HeadTerm n) h
  where
    sig = do
      (n, u) <- new_notion; is; (q, f) <- anotion -|- noInfo
      let v = zVar u; fn = replace v (trm n)
      h <- liftM (fn . q) $ dig f [v]
      return ((n,h),u)

    noInfo =
      art >> wd_tokenOf ["notion", "function", "constant"] >> return (id,Top)
    trm Trm {trName = "=", trArgs = [_,t]} = t; trm t = t

new_predicat = do n <- new_prd_pattern nvr; MS.get >>= addExpr n n True

new_notion = do
  (n, u) <- new_ntn_pattern nvr;
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
    disVs ls (Var v@('h':_) _ : vs)  = notElem v ls && disVs (v:ls) vs
    disVs ls (Var v@('x':_) _ : vs)  = notElem v ls && disVs (v:ls) vs
    disVs _ [] = True
    disVs _ _ = False



--- introduce synonyms


nonLogicalLanguageExt =
  introduceSynonym </> pretypeVariable </> introduceMacro

introduceSynonym = sym >>= MS.modify . upd >> return ()
  where
    upd ss st = st { str_syms = ss : str_syms st }

    sym = exbrk $ do
      w <- word ; root <- optLL1 w $ sfx w; sm_token "/"
      syms <- (wlexem -|- sfx w) `sepByLL1` sm_token "/"
      return $ root : syms
    sfx w = sm_token "-" >> liftM (w ++) word


pretypeVariable = narrow typeVar >>= MS.modify . upd >> return ()
  where
    typeVar = do
      wd_token "let"; vs@(_:_) <- varlist; standFor;
      g <- wellFormedCheck (overfree []) (dot holedNotion)
      return (vs, ignoreNames g)

    holedNotion = do (q, f) <- anotion; liftM q $ dig f [zHole]

    upd tv st = st { tvr_expr = tv : tvr_expr st }


introduceMacro = do
  (f, g) <- wd_token "let" >> narrow (prd -|- ntn)
  MS.get >>= addExpr f (ignoreNames g) False
  return ()
  where
    prd = wellFormedCheck prdVars $ do
      f <- new_prd_pattern avr
      g <- standFor >> dot statement; return (f, g)
    ntn = wellFormedCheck funVars $ do
      (n, u) <- unnamedNotion avr
      (q, f) <- standFor >> dot anotion
      h <- liftM q $ dig f [zVar u]; return (n, h)

ignoreNames (All _ f) = All "" $ ignoreNames f
ignoreNames (Exi _ f) = Exi "" $ ignoreNames f
ignoreNames f@Trm{}   = f
ignoreNames f         = mapF ignoreNames f
