{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Pattern parsing and pattern state management.
-}



module SAD.ForTheL.Pattern where


import qualified Control.Monad.State.Class as MS

import SAD.ForTheL.Base

import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Parser.Token
import SAD.Parser.Primitives


import SAD.Data.Formula

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
    n = idCount st;
    (pt, nf) = extractWordPattern st (giveId p n t) f
    fm  = substs nf $ map trName vs
    ns  = st { adjExpr = (pt, fm) : adjExpr st, idCount = incId p n}

addExpr t@Trm {trName = 'd':'o':' ':_, trArgs = vs} f p st =
  MS.put ns >> return nf
  where
    n = idCount st;
    (pt, nf) = extractWordPattern st (giveId p n t) f
    fm = substs nf $ map trName vs
    ns = st {verExpr = (pt, fm) : verExpr st, idCount = incId p n}

addExpr t@Trm {trName = 'm':'i':'s':' ':_, trArgs = vs} f p st =
  MS.put ns >> return nf
  where
    n = idCount st;
    ((hp:tp), nf) = extractWordPattern st (giveId p n t) f
    pt = hp : Wd [] : Vr : tp
    fm = substs nf $ map trName vs
    ns = st {adjExpr = (pt, fm) : adjExpr st, idCount = incId p n}

addExpr t@Trm {trName = 'm':'d':'o':' ':_, trArgs = vs} f p st =
  MS.put ns >> return nf
  where
    n = idCount st;
    ((hp:tp), nf) = extractWordPattern st (giveId p n t) f
    pt = hp : Wd [] : Vr : tp
    fm = substs nf $ map trName vs
    ns = st {verExpr = (pt, fm) : verExpr st, idCount = incId p n}

addExpr t@Trm {trName = 'a':' ':_, trArgs = vs} f p st =
  MS.put ns >> return nf
  where
    n = idCount st;
    (pt, nf) = extractWordPattern st (giveId p n t) f
    fm = substs nf $ map trName vs
    ns = st {ntnExpr = (pt, fm) : ntnExpr st, idCount = incId p n}

addExpr Trm {trName= "=", trArgs = [v, t@Trm {trName = 'a':' ':rs}]} f p st =
  MS.put ns >> return nf
  where
    n = idCount st; vs = trArgs t
    (pt, nf) = extractWordPattern st (giveId p n t {trName = "tthe " ++ rs}) f
    fm = substs nf $ map trName (v:vs)
    ns = st {ntnExpr = (pt, fm) : ntnExpr st, idCount = incId p n}

addExpr Trm {trName = "=", trArgs = [_, t]} eq@Trm {trName = "="} p st =
  MS.put nn >> return (zEqu v nf)
  where
    [v, f] = trArgs eq; vs = trArgs t
    n = idCount st
    (pt, nf) = extractSymbPattern (giveId p n t) f
    fm = substs nf $ map trName vs
    -- classification of pattern
    csm = lsm && rsm; lsm = notVr (head pt); rsm = notVr (last pt)
    notVr Vr = False; notVr _ = True
    -- add to the right category
    ns | csm = st {cfnExpr = (pt, fm) : cfnExpr st}
       | lsm = st {lfnExpr = (init pt, fm) : lfnExpr st}
       | rsm = st {rfnExpr = (tail pt, fm) : rfnExpr st}
       | otherwise = st {ifnExpr = (init (tail pt), fm) : ifnExpr st}
    -- increment id counter
    nn = ns {idCount = incId p n}


addExpr t@Trm {trName = s, trArgs = vs} f p st =
  MS.put nn >> return nf
  where
    n = idCount st
    (pt, nf) = extractSymbPattern (giveId p n t) f
    fm = substs nf $ map trName vs
    -- classification of pattern
    csm = lsm && rsm; lsm = notVr (head pt); rsm = notVr (last pt)
    notVr Vr = False; notVr _ = True
    -- add the pattern to the right category
    ns | csm = st {cprExpr = (pt, fm) : cprExpr st}
       | lsm = st {lprExpr = (init pt, fm) : lprExpr st}
       | rsm = st {rprExpr = (tail pt, fm) : rprExpr st}
       | otherwise = st {iprExpr = (init (tail pt), fm) : iprExpr st}
    -- check if pattern is a symbolic notion
    snt = not lsm && elem (trName $ head vs) (declNames [] nf)
    -- and add it there as well if so (and increment id counter)
    nn | snt = ns {sntExpr = (tail pt,fm) : sntExpr st, idCount = incId p n}
       | otherwise = ns {idCount = incId p n}






-- pattern extraction

extractWordPattern st t@Trm {trName = s, trArgs = vs} f = (pt, nf)
  where
    pt = map getPatt ws
    nt = t {trName = pr ++ getName pt}
    nf = replace nt t {trId = newId} f
    (pr:ws) = words s
    dict = strSyms st

    getPatt "." = Nm
    getPatt "#" = Vr
    getPatt w = Wd $ foldl union [w] $ filter (elem w) dict

    getName (Wd ((c:cs):_):ls) = toUpper c : cs ++ getName ls
    getName (_:ls) = getName ls
    getName [] = ""


extractSymbPattern t@Trm {trName = s, trArgs = vs} f = (pt, nf)
  where
    pt = map getPatt (words s)
    nt = t {trName ='s' : getName pt}
    nf = replace nt t {trId = newId} f

    getPatt "#" = Vr
    getPatt w = Sm w

    getName (Sm s:ls) = symEncode s ++ getName ls
    getName (Vr:ls) = symEncode "." ++ getName ls
    getName [] = ""




-- New patterns


newPrdPattern tvr = multi </> unary </> newSymbPattern tvr
  where
    unary = do
      v <- tvr; (t, vs) <- unaryAdj -|- unaryVerb
      return $ zTrm newId t (v:vs)
    multi = do
      (u,v) <- liftM2 (,) tvr (comma >> tvr);
      (t, vs) <- multiAdj -|- multiVerb
      return $ zTrm newId t (u:v:vs)

    unaryAdj = do is; (t, vs) <- ptHead wlexem tvr; return ("is " ++ t, vs)
    multiAdj = do is; (t, vs) <- ptHead wlexem tvr; return ("mis " ++ t, vs)
    unaryVerb = do (t, vs) <- ptHead wlexem tvr; return ("do " ++ t, vs)
    multiVerb = do (t, vs) <- ptHead wlexem tvr; return ("mdo " ++ t, vs)

newNtnPattern tvr = (ntn <|> fun) </> unnamedNotion tvr
  where
    ntn = do
      an; (t, v:vs) <- ptName wlexem tvr
      return (zTrm newId ("a " ++ t) (v:vs), (trName v, trPosition v))
    fun = do
      the; (t, v:vs) <- ptName wlexem tvr
      return (zEqu v $ zTrm newId ("a " ++ t) vs, (trName v, trPosition v))

unnamedNotion tvr = (ntn <|> fun) </> (newSymbPattern tvr >>= equ)
  where
    ntn = do
      an; (t, v:vs) <- ptNoName wlexem tvr
      return (zTrm newId ("a " ++ t) (v:vs), (trName v, trPosition v))
    fun = do
      the; (t, v:vs) <- ptNoName wlexem tvr
      return (zEqu v $ zTrm newId ("a " ++ t) vs, (trName v, trPosition v))
    equ t = do v <- hidden; return (zEqu (pVar v) t, v)


newSymbPattern tvr = left -|- right
  where
    left = do
      (t, vs) <- ptHead slexem tvr
      return $ zTrm newId t vs
    right = do
      (t, vs) <- ptTail slexem tvr
      guard $ not $ null $ tail $ words t
      return $ zTrm newId t vs


-- pattern parsing


ptHead lxm tvr = do
  l <- unwords <$> chain lxm
  (ls, vs) <- opt ([], []) $ ptTail lxm tvr
  return (l ++ ' ' : ls, vs)


ptTail lxm tvr = do
  v <- tvr
  (ls, vs) <- opt ([], []) $ ptHead lxm tvr
  return ("# " ++ ls, v:vs)


ptName lxm tvr = do
  l <- unwords <$> chain lxm; n <- nam
  (ls, vs) <- opt ([], []) $ ptHead lxm tvr
  return (l ++ " . " ++ ls, n:vs)


ptNoName lxm tvr = do
  l <- unwords <$> chain lxm; n <- hid
  (ls, vs) <- opt ([], []) $ ptShort lxm tvr
  return (l ++ " . " ++ ls, n:vs)
  where
    --ptShort is a kind of buffer that ensures that a variable does not directly
    --follow the name of the notion
    ptShort lxm tvr = do
      l <- lxm; (ls, vs) <- ptTail lxm tvr
      return (l ++ ' ' : ls, vs)



-- In-pattern lexemes and variables

wlexem = do
  l <- wlx
  guard $ all isAlpha l
  return $ map toLower l

slexem = slex -|- wlx
  where
    slex = tokenPrim isSymb
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
  v <- var; dvs <- getDecl; tvs <- MS.gets tvrExpr
  guard $ fst v `elem` dvs || any (elem (fst v) . fst) tvs
  return $ pVar v

avr = do
  v <- var; guard $ null $ tail $ tail $ fst v
  return $ pVar v

nam = do
  n <- fmap (const Top) nvr </> avr
  guard $ isVar n ; return n

hid = fmap pVar hidden
