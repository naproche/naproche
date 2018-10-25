{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

FoTheL state and state management, parsing of primitives, operations on variables and macro expressions.
-}



module Alice.ForTheL.Base where

import Control.Monad
import qualified Control.Monad.State.Class as MS
import Data.Char
import Data.List

import Alice.Data.Formula

import Alice.Parser.Base
import Alice.Parser.Combinators
import Alice.Parser.Primitives

import Debug.Trace
import Alice.Parser.Token


type FTL = Parser FState


type UTerm    = (Formula -> Formula, Formula)

type UNotion  = (Formula -> Formula, Formula, String)

type MTerm    = (Formula -> Formula, [Formula])
type MNotion  = (Formula -> Formula, Formula, [String])

type Prim     = ([Patt], [Formula] -> Formula)


data FState = FState {
  adj_expr, ver_expr, ntn_expr, snt_expr :: [Prim],
  cfn_expr, rfn_expr, lfn_expr, ifn_expr :: [Prim],
  cpr_expr, rpr_expr, lpr_expr, ipr_expr :: [Prim],

  tvr_expr :: [TVar], str_syms :: [[String]], var_decl :: [String],
  id_count :: Int, in_decl :: Bool, hid_count :: Int }



initFS  = FState  eq [] nt sn
                  cf rf [] []
                  [] [] [] sp
                  [] [] [] 0 False 0
  where
    eq  = [ ([Wd ["equal"], Wd ["to"], Vr], zTrm (-1) "="),
            ([Wd ["nonequal"], Wd ["to"], Vr], Not . zTrm (-1) "=") ]
    sp  = [ ([Sm "="], zTrm (-1) "="),
            ([Sm "!", Sm "="], Not . zTrm (-1) "="),
            ([Sm "-", Sm "<", Sm "-"], zTrm (-2) "iLess"),
            ([Sm "-~-"], \(m:n:_) -> zAll "" $ Iff (zElem (zVar "") m) (zElem (zVar "") n)) ]
    sn  = [ ([Sm "=", Vr], zTrm (-1) "=") ]
    nt  = [ ([Wd ["function","functions"], Nm], zFun . head),
            ([Wd ["set","sets"], Nm], zSet . head),
            ([Wd ["element", "elements"], Nm, Wd ["of"], Vr], \(x:m:_) -> zElem x m),
            ([Wd ["object", "objects"], Nm], zObj . head)]
    rf  = [ ([Sm "[", Vr, Sm "]"], \(f:x:_) -> zApp f x)]
    cf  = [ ([Sm "Dom", Sm "(",Vr,Sm ")"], zDom . head),
            ([Sm "(", Vr, Sm ",", Vr, Sm ")"], \(x:y:_) -> zPair x y) ]




getExpr :: (FState -> [a]) -> (a -> FTL b) -> FTL b
getExpr e p = MS.gets e >>= tryAll . map (unexpectedUnit . try . p)


getDecl :: FTL [String]
getDecl = MS.gets var_decl

addDecl :: [String] -> FTL a -> FTL a
addDecl vs p  = do
  dcl <- MS.gets var_decl; MS.modify adv;
  after p $ MS.modify $ sbv dcl
  where
    adv s     = s { var_decl = vs ++ var_decl s }
    sbv vs s  = s { var_decl = vs }

getPretyped :: FTL [TVar]
getPretyped = MS.gets tvr_expr

-- Predicates: verbs and adjectives

prim_ver, prim_adj, prim_un_adj :: FTL UTerm -> FTL UTerm

prim_ver      = getExpr ver_expr . prim_prd
prim_adj      = getExpr adj_expr . prim_prd
prim_un_adj   = getExpr (filter (unary . fst) . adj_expr) . prim_prd
  where
    unary pt  = Vr `notElem` pt

prim_prd p (pt, fm) = do  (q, ts) <- wd_patt p pt
                          return (q, fm $ zHole:ts)


-- Multi-subject predicates: [a,b are] equal

prim_m_ver, prim_m_adj, prim_m_un_adj :: FTL UTerm -> FTL UTerm

prim_m_ver    = getExpr ver_expr . prim_ml_prd
prim_m_adj    = getExpr adj_expr . prim_ml_prd
prim_m_un_adj = getExpr (filter (unary . fst) . adj_expr) . prim_ml_prd
  where
    unary (Vr : pt) = Vr `notElem` pt
    unary (_  : pt) = unary pt
    unary _         = True

prim_ml_prd p (pt, fm)  = do  (q, ts) <- ml_patt p pt
                              return (q, fm $ zHole:zSlot:ts)


-- Notions and functions

prim_ntn, prim_of_ntn :: FTL UTerm -> FTL MNotion

prim_ntn p  = getExpr ntn_expr ntn
  where
    ntn (pt, fm)  = do  (q, vs, ts) <- nt_patt p pt
                        return (q, fm $ zHole:ts, vs)

prim_of_ntn p = getExpr ntn_expr ntn
  where
    ntn (pt, fm)  = do  (q, vs, ts) <- of_patt p pt
                        let fn v = fm $ (zVar v):zHole:ts
                        return (q, foldr1 And $ map fn vs, vs)

prim_cm_ntn :: FTL UTerm -> FTL MTerm -> FTL MNotion
prim_cm_ntn p s = getExpr ntn_expr ntn
  where
    ntn (pt, fm)  = do  (q, vs, as, ts) <- cm_patt p s pt
                        let fn v = fm $ zHole:v:ts
                        return (q, foldr1 And $ map fn as, vs)

prim_fun :: FTL UTerm -> FTL UTerm
prim_fun  = (>>= fun) . prim_ntn
  where
    fun (q, Trm {trName = "=", trArgs = [_, t]}, _) | not (occursH t) = return (q, t)
    fun _ = mzero


-- Symbolic primitives

prim_cpr  = getExpr cpr_expr . prim_csm     -- T ... T
prim_rpr  = getExpr rpr_expr . prim_rsm     -- v ... T
prim_lpr  = getExpr lpr_expr . prim_lsm     -- T ... v
prim_ipr  = getExpr ipr_expr . prim_ism     -- v ... v

prim_cfn  = getExpr cfn_expr . prim_csm
prim_rfn  = getExpr rfn_expr . prim_rsm
prim_lfn  = getExpr lfn_expr . prim_lsm
prim_ifn  = getExpr ifn_expr . prim_ism

prim_csm p (pt, fm) = sm_patt p pt >>= \l -> return $ fm l
prim_rsm p (pt, fm) = sm_patt p pt >>= \l -> return $ \t -> fm $ t:l
prim_lsm p (pt, fm) = sm_patt p pt >>= \l -> return $ \s -> fm $ l++[s]
prim_ism p (pt, fm) = sm_patt p pt >>= \l -> return $ \t s -> fm $ t:l++[s]
prim_snt :: FTL Formula -> FTL MNotion
prim_snt p  = noError $ varlist >>= getExpr snt_expr . snt
  where
    snt vs (pt, fm) = sm_patt p pt >>= \l -> return (id, fm $ zHole:l, vs)




data Patt = Wd [String] | Sm String | Vr | Nm deriving (Eq, Show)
 -- I added the deriving Show

samePat [] [] = True
samePat ((Wd ls) : rst1) ((Wd rs) : rst2) = all (`elem` rs) ls && samePat rst1 rst2
samePat (Vr : rst1) (Vr : rst2) = samePat rst1 rst2
samePat (Nm : rst1) (Nm : rst2) = samePat rst1 rst2
samePat ((Sm s) : rst1) ((Sm t) : rst2) = s == t && samePat rst1 rst2
samePat _ _ = False




-- most basic pattern parser: simply follow the pattern anf parse terms with p
-- at variable places
wd_patt p (Wd l : ls) = wd_tokenOf l >> wd_patt p ls
wd_patt p (Vr : ls)   = do  (r, t) <- p
                            (q, ts) <- wd_patt p ls
                            return (r . q, t:ts)
wd_patt _ []          = return (id, [])
wd_patt _ _           = mzero

-- parses a symbolic pattern
sm_patt p (Vr : ls)   = liftM2 (:) p $ sm_patt p ls
sm_patt p (Sm s : ls) = sm_token s >> sm_patt p ls
sm_patt _ []          = return []
sm_patt _ _           = mzero

-- parses a multi-subject pattern: follow the pattern, but ignore the wd_token
-- right before the first variable. Then check that all "and" tokens have been
-- consumed. Example pattern: [Wd ["commute","commutes"], Wd ["with"], Vr]. Then we can parse
-- "a commutes with c and d" as well as "a and b commute".
ml_patt p (Wd l :_: Vr : ls)
                      = wd_tokenOf l >> na_patt p ls
ml_patt p (Wd l : ls) = wd_tokenOf l >> ml_patt p ls
ml_patt _ _           = mzero


-- parses a notion: follow the pattern to the name place, record names,
-- then keep following the pattern
nt_patt p (Wd l : ls) = wd_tokenOf l >> nt_patt p ls
nt_patt p (Nm : ls)   = do  vs <- namlist
                            (q, ts) <- wd_patt p ls
                            return (q, vs, ts)
nt_patt _ _           = mzero

-- parse an "of"-notion: follow the pattern to the notion name, then check that
-- "of" follows the name followed by a variable that is not followed by "and"
of_patt p (Wd l : ls) = wd_tokenOf l >> of_patt p ls
of_patt p (Nm : Wd l : Vr : ls)
                      = do  guard $ elem "of" l; vs <- namlist
                            (q, ts) <- na_patt p ls
                            return (q, vs, ts)
of_patt _ _           = mzero

-- parse a "common"-notion: basically like the above. We use the special parser
-- s for the first variable place after the "of" since we expect multiple terms
-- here. Example: A common *divisor of m and n*.
cm_patt p s (Wd l:ls) = wd_tokenOf l >> cm_patt p s ls
cm_patt p s (Nm : Wd l : Vr : ls)
                      = do  guard $ elem "of" l; vs <- namlist; wd_tokenOf l
                            (r, as) <- s; when (null $ tail as) $
                              fail "several objects expected for `common'"
                            (q, ts) <- na_patt p ls
                            return (r . q, vs, as, ts)
cm_patt _ _ _         = mzero

-- an auxiliary pattern parser that checks that we are not dealing wiht an "and"
-- wd_token and then continues to follow the pattern
na_patt p (Wd l : ls) = guard (not $ elem "and" l) >> wd_tokenOf l >> wd_patt p ls
na_patt p ls          = wd_patt p ls



-- Variables

namlist = varlist -|- liftM (:[]) hidden

varlist = do  vs <- var `sepBy` wd_token ","
              nodups vs ; return vs

nodups vs = unless ((null :: [b] -> Bool) $ dups vs) $
              fail $ "duplicate names: " ++ show vs

hidden  = do n <- MS.gets hid_count
             MS.modify $ \st -> st {hid_count = succ n}
             return ('h':show n)

var     = do v <- satisfy (\s -> all isAlphaNum s && isAlpha (head s))
             return ('x':v)

--- pretyped Variables

type TVar = ([String], Formula)

prim_tvr :: FTL MNotion
prim_tvr  = getExpr tvr_expr tvr
  where
    tvr (vr, nt)  = do  vs <- varlist
                        guard $ all (`elem` vr) vs
                        return (id, nt, vs)

-- free

freeVars f = do dvs <- getDecl; return $ free dvs f

--- decl

decl vs = dive
  where
    dive (All _ f)  = dive f
    dive (Exi _ f)  = dive f
    dive (Tag _ f)  = dive f
    dive (Imp f g)  = filter (noc f) (dive g)
    dive (And f g)  = dive f `union` filter (noc f) (dive g)
    dive Trm {trName = 'a':_, trArgs = v@Var{trName = u@('x':_)}:ts}
      | all (not . occurs v) ts = nifilt vs u
    dive Trm{trName = "=", trArgs = [v@Var{trName = u@('x':_)}, t]}
      | isTrm t && not (occurs v t) = nifilt vs u
    dive _  = []

    noc f v = not $ occurs (zVar v) f


overfree :: [String] -> Formula -> Maybe String
overfree vs f
    | occurs zSlot f  = Just $ "too few subjects for an m-predicate " ++ inf
    | not (null sbs)  = Just $ "free undeclared variables: "   ++ sbs ++ inf
    | not (null ovl)  = Just $ "overlapped variables: "        ++ ovl ++ inf
    | otherwise       = Nothing
  where
    sbs = unwords $ map showVar $ free vs f
    ovl = unwords $ map showVar $ over vs f
    inf = "\n in translation: " ++ show f

    over vs (All v f) = bvrs vs v f
    over vs (Exi v f) = bvrs vs v f
    over vs f = foldF (over vs) f

    bvrs vs v f | elem v vs = [v]
                | null v    = over vs f
                | otherwise = over (v:vs) f


--- macro expressions


comma = wd_tokenOf [",", "and"]
is    = wd_tokenOf ["is", "be", "are"]
art = opt () $ wd_tokenOf ["a","an","the"]
an = wd_tokenOf ["a", "an"]
the = wd_token "the"
iff = wd_token "iff" <|> mapM_ wd_token ["if", "and", "only", "if"]
that  = wd_token "that"
standFor = wd_token "denote" <|> (wd_token "stand" >> wd_token "for")
arrow = symbol "->"
there = wd_token "there" >> wd_tokenOf ["is","exist","exists"]
does = opt () $ wd_tokenOf ["does", "do"]
has = wd_tokenOf ["has" , "have"]
with  = wd_tokenOf ["with", "of", "having"]
such  = wd_tokenOf ["such", "so"]


--just for now:

showVar ('x':nm) = nm
showVar nm = nm
