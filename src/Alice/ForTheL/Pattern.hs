{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Pattern parsing and pattern state management.
-}



module Alice.ForTheL.Pattern where


import qualified Control.Monad.State.Class as MS

import Alice.ForTheL.Base

import Alice.Parser.Base
import Alice.Parser.Combinators
import Alice.Parser.Token
import Alice.Parser.Primitives


import Alice.Data.Formula

import Data.List
import Data.Char
import Control.Monad


import Debug.Trace
-- add expressions to the state of ForTheL


giveId p n t = t {trId = if p then n else (trId t)}
incId p n = if p then succ n else n

addExpr :: Formula -> Formula -> Bool -> FState -> FTL Formula

addExpr t@Trm {trName = 'i':'s':' ':_, trArgs = vs} f p st =
  MS.put ns >> return nf
  where
    n = id_count st;
    (pt, nf) = extractWordPattern st (giveId p n t) f
    fm  = substs nf $ map trName vs
    ns  = st { adj_expr = (pt, fm) : adj_expr st, id_count = incId p n}

addExpr t@Trm {trName = 'd':'o':' ':_, trArgs = vs} f p st =
  MS.put ns >> return nf
  where
    n = id_count st;
    (pt, nf) = extractWordPattern st (giveId p n t) f
    fm = substs nf $ map trName vs
    ns = st {ver_expr = (pt, fm) : ver_expr st, id_count = incId p n}

addExpr t@Trm {trName = 'm':'i':'s':' ':_, trArgs = vs} f p st =
  MS.put ns >> return nf
  where
    n = id_count st;
    ((hp:tp), nf) = extractWordPattern st (giveId p n t) f
    pt = hp : Wd [] : Vr : tp
    fm = substs nf $ map trName vs
    ns = st {adj_expr = (pt, fm) : adj_expr st, id_count = incId p n}

addExpr t@Trm {trName = 'm':'d':'o':' ':_, trArgs = vs} f p st =
  MS.put ns >> return nf
  where
    n = id_count st;
    ((hp:tp), nf) = extractWordPattern st (giveId p n t) f
    pt = hp : Wd [] : Vr : tp
    fm = substs nf $ map trName vs
    ns = st {ver_expr = (pt, fm) : ver_expr st, id_count = incId p n}

addExpr t@Trm {trName = 'a':' ':_, trArgs = vs} f p st =
  MS.put ns >> return nf
  where
    n = id_count st;
    (pt, nf) = extractWordPattern st (giveId p n t) f
    fm = substs nf $ map trName vs
    ns = st {ntn_expr = (pt, fm) : ntn_expr st, id_count = incId p n}

addExpr Trm {trName= "=", trArgs = [v, t@Trm {trName = 'a':' ':rs}]} f p st =
  MS.put ns >> return nf
  where
    n = id_count st; vs = trArgs t
    (pt, nf) = extractWordPattern st (giveId p n t {trName = "tthe " ++ rs}) f
    fm = substs nf $ map trName (v:vs)
    ns = st {ntn_expr = (pt, fm) : ntn_expr st, id_count = incId p n}

addExpr Trm {trName = "=", trArgs = [_, t]} eq@Trm {trName = "="} p st =
  MS.put nn >> return (zEqu v nf)
  where
    [v, f] = trArgs eq; vs = trArgs t
    n = id_count st
    (pt, nf) = extractSymbPattern (giveId p n t) f
    fm = substs nf $ map trName vs
    -- classification of pattern
    csm = lsm && rsm; lsm = notVr (head pt); rsm = notVr (last pt)
    notVr Vr = False; notVr _ = True
    -- add to the right category
    ns | csm  = st {cfn_expr = (pt, fm) : cfn_expr st}
       | lsm  = st {lfn_expr = (init pt, fm) : lfn_expr st}
       | rsm  = st {rfn_expr = (tail pt, fm) : rfn_expr st}
       | True = st {ifn_expr = (init (tail pt), fm) : ifn_expr st}
    -- increment id counter
    nn = ns {id_count = incId p n}


addExpr t@Trm {trName = s, trArgs = vs} f p st =
  MS.put nn >> return nf
  where
    n = id_count st
    (pt, nf) = extractSymbPattern (giveId p n t) f
    fm = substs nf $ map trName vs
    -- classification of pattern
    csm = lsm && rsm; lsm = notVr (head pt); rsm = notVr (last pt)
    notVr Vr = False; notVr _ = True
    -- add the pattern to the right category
    ns | csm  = st {cpr_expr = (pt, fm) : cpr_expr st}
       | lsm  = st {lpr_expr = (init pt, fm) : lpr_expr st}
       | rsm  = st {rpr_expr = (tail pt, fm) : rpr_expr st}
       | True = st {ipr_expr = (init (tail pt), fm) : ipr_expr st}
    -- check if pattern is a symbolic notion
    snt = not lsm && elem (trName $ head vs) (decl [] nf)
    -- and add it there as well if so (and increment id counter)
    nn | snt  = ns {snt_expr = (tail pt,fm) : snt_expr st, id_count = incId p n}
       | True = ns {id_count = incId p n}






-- pattern extraction

extractWordPattern st t@Trm {trName = s, trArgs = vs} f = (pt, nf)
  where
    pt  = map get_patt ws
    nt  = t {trName = pr ++ get_name pt}
    nf  = replace nt t {trId = newId} f
    (pr:ws) = words s
    dict = str_syms st

    get_patt "." = Nm
    get_patt "#" = Vr
    get_patt  w  = Wd $ foldl union [w] $ filter (elem w) dict

    get_name (Wd ((c:cs):_):ls) = toUpper c : cs ++ get_name ls
    get_name (_:ls)             = get_name ls
    get_name []                 = ""


extractSymbPattern t@Trm {trName = s, trArgs = vs} f = (pt, nf)
  where
    pt  = map get_patt (words s)
    nt  = t {trName ='s' : get_name pt}
    nf  = replace nt t {trId = newId} f

    get_patt "#" = Vr
    get_patt  w  = Sm w

    get_name (Sm s:ls)  = symEncode s ++ get_name ls
    get_name (Vr:ls)    = symEncode "." ++ get_name ls
    get_name []         = ""




-- New patterns


new_prd_pattern tvr = multi </> unary </> new_symb_pattern tvr
  where
    unary = do
      v <- tvr; (t, vs) <- unary_adj -|- unary_verb
      return $ zTrm newId t (v:vs)
    multi = do
      (u,v) <- liftM2 (,) tvr (comma >> tvr);
      (t, vs) <- multi_adj -|- multi_verb
      return $ zTrm newId t (u:v:vs)

    unary_adj  = do is; (t, vs) <- pt_head wlexem tvr; return ("is "  ++ t, vs)
    multi_adj  = do is; (t, vs) <- pt_head wlexem tvr; return ("mis " ++ t, vs)
    unary_verb = do (t, vs) <- pt_head wlexem tvr; return ("do "  ++ t, vs)
    multi_verb = do (t, vs) <- pt_head wlexem tvr; return ("mdo " ++ t, vs)

new_ntn_pattern tvr = (ntn <|> fun) </> unnamedNotion tvr
  where
    ntn = do
      an;  (t, v:vs) <- pt_name wlexem tvr
      return (zTrm newId ("a " ++ t) (v:vs), trName v)
    fun = do
      the; (t, v:vs) <- pt_name wlexem tvr
      return (zEqu v $ zTrm newId ("a " ++ t) vs, trName v)

unnamedNotion tvr = (ntn <|> fun) </> (new_symb_pattern tvr >>= equ)
  where
    ntn = do
      an;  (t, v:vs) <- pt_nonm wlexem tvr
      return (zTrm newId ("a " ++ t) (v:vs), trName v)
    fun = do
      the; (t, v:vs) <- pt_nonm wlexem tvr
      return (zEqu v $ zTrm newId ("a " ++ t) vs, trName v)
    equ t = do v <- hidden; return (zEqu (zVar v) t, v)


new_symb_pattern tvr = left -|- right
  where
    left  = do
      (t, vs) <- pt_head slexem tvr
      return $ zTrm newId t vs
    right = do
      (t, vs) <- pt_tail slexem tvr
      guard $ not $ null $ tail $ words t
      return $ zTrm newId t vs


-- pattern parsing


pt_head lxm tvr = do
  l <- liftM unwords $ chain lxm
  (ls, vs) <- opt ([], []) $ pt_tail lxm tvr
  return (l ++ ' ' : ls, vs)


pt_tail lxm tvr = do
  v <- tvr
  (ls, vs) <- opt ([], []) $ pt_head lxm tvr
  return ("# " ++ ls, v:vs)


pt_name lxm tvr = do
  l <- liftM unwords $ chain lxm; n <- nam
  (ls, vs) <- opt ([], []) $ pt_head lxm tvr
  return (l ++ " . " ++ ls, n:vs)


pt_nonm lxm tvr = do
  l <- liftM unwords $ chain lxm; n <- hid
  (ls, vs) <- opt ([], []) $ pt_shot lxm tvr
  return (l ++ " . " ++ ls, n:vs)
  where
    pt_shot lxm tvr = do --pt_shot is a kind of buffer that ensures that a variable does not directly follow the name of the notion
      l <- lxm; (ls, vs) <- pt_tail lxm tvr
      return (l ++ ' ' : ls, vs)



-- In-pattern lexemes and variables

wlexem  = do
  l <- wlx
  guard $ all isAlpha l
  return $ map toLower l

slexem  = slex -|- wlx
  where
    slex  = tokenPrim isSymb
    isSymb t =
      let tk = showToken t; ltk = map toLower tk
      in  case tk of
            [c] -> guard (c `elem` symChars) >> return tk
            _   -> Nothing

wlx = failing nvr >> tokenPrim isWord
  where
    isWord t =
      let tk = showToken t; ltk = map toLower tk
      in guard (all isAlphaNum tk && ltk `notElem` keylist) >> return tk
    keylist = ["a","an","the","is","are","be"]

nvr = do
  v <- var; dvs <- getDecl; tvs <- MS.gets tvr_expr
  guard $ v `elem` dvs || any (elem v . fst) tvs
  return $ zVar v

avr = do
  v <- var; guard $ null $ tail $ tail v
  return $ zVar v

nam = do
  n <- liftM (const Top) nvr </> avr
  guard $ isVar n ; return n

hid = liftM zVar hidden
