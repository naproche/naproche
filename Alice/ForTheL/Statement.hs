{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Syntax of ForThel statements.
-}



module Alice.ForTheL.Statement (
  statement,
  var, s_var, s_term,
  anotion, dig, selection, setNotion, functionNotion) where

import Alice.ForTheL.Base
import Alice.Parser.Base
import Alice.Parser.Combinators

import Alice.Parser.Token

import Alice.Data.Base
import Alice.Data.Formula
import Alice.Data.Kit

import Debug.Trace
import qualified Control.Monad.State.Class as MS
import Data.Function ((&))


import Control.Monad

statement = headed <|> chained

headed = qu_statem <|> if_then_statem <|> wrong_statem
  where
    qu_statem      = liftM2 ($) qu_chain statement
    if_then_statem = liftM2 Imp (wd_token "if" >> statement) (wd_token "then" >> statement)
    wrong_statem   = mapM_ wd_token ["it", "is", "wrong", "that"] >> liftM Not statement



chained = label "chained statement" $ andOr <|> neitherNor >>= chainEnd
  where
    andOr      = atomic >>= \f -> opt f (andChain f <|> orChain f)
    andChain f =
      liftM (foldl And f) $ wd_token "and" >> atomic `sepBy` wd_token "and"
    -- we take sepBy here instead of sepByLLx since we do not  know if the
    -- and/or wd_token binds to this statement or to an ambient one
    orChain  f = liftM (foldl Or  f) $ wd_token "or"  >> atomic `sepBy` wd_token "or"

    neitherNor = do
      wd_token "neither"; f <- atomic; wd_token "nor"
      fs <- atomic `sepBy` wd_token "nor"
      return $ foldl1 And $ map Not (f:fs)


chainEnd f = optLL1 f $ and_st <|> or_st <|> iff_st <|> where_st
  where
    and_st   = liftM (And f) $ wd_token "and" >> headed
    or_st    = liftM (Or  f) $ wd_token "or"  >> headed
    iff_st   = liftM (Iff f) $ iff            >> statement
    where_st = do wd_tokenOf ["when", "where"]; y <- statement
                  return $ foldr zAll (Imp y f) (decl [] y)


atomic = label "atomic statement"
  thereIs <|> (simple </> (wehve >> sm_form <|> thesis))
  where
    wehve = optLL1 () $ wd_token "we" >> wd_token "have"

thesis = art >> (thes <|> contrary <|> contradiction)
  where
    thes          = wd_token "thesis"        >> return zThesis
    contrary      = wd_token "contrary"      >> return (Not zThesis)
    contradiction = wd_token "contradiction" >> return Bot

thereIs = there >> (noNotion -|- notions)
  where
    noNotion = do wd_token "no"; (q, f, vs) <- notion;
                  return $ Not $ foldr mbExi (q f) vs
    notions  = liftM multExi $ art >> notion `sepBy` comma




simple = label "simple statement" $
  do (q, ts) <- terms; p <- conj_chain does_predicat;
      q' <- optLL1 id qu_chain;
      -- this part is not in the language description
      -- example: x = y *for every real number x*.
      liftM (q . q') $ dig p ts

sm_form = liftM2 (flip ($)) (s_form -|- classEq) $ optLL1 id qu_chain

--- predicates


does_predicat = label "does predicat" $
  (does >> (doP -|- m_doP)) <|> hasP <|> isChain
  where
    doP     = predicat   prim_ver
    m_doP   = m_predicat prim_m_ver
    hasP    = has >> has_predicat
    isChain = is  >> conj_chain (isA_predicat -|- is_predicat)


is_predicat = label "is predicat" $
  pAdj -|- p_m_Adj -|- (with >> has_predicat)
  where
    pAdj    = predicat   prim_adj
    p_m_Adj = m_predicat prim_m_adj


isA_predicat = label "isA predicat" $
  not_ntn <|> ntn
  -- Unlike the langugae description, we distinguish positive and negative
  -- rather than notions and fixed terms
  where
    ntn     = liftM (uncurry ($)) anotion
    not_ntn = do
      wd_token "not"; (q, f) <- anotion; let unfinished = dig f [zHole]
      optLLx (q $ Not f) $ liftM (q. Tag DIG . Not) unfinished

has_predicat = label "has predicat" $
  no_possessive <|> possessive
  where
    possessive = art >> common <|> unary
    unary      = liftM (Tag DIG . multExi) $ possess `sepBy` (comma >> art)
    common     = wd_token "common" >> (liftM multExi $ (liftM digadd possess) `sepBy` comma)

    no_possessive = n_unary -|- n_common
    n_unary  = do
      wd_token "no"; (q, f, v) <- possess;
      return $ q . Tag DIG . Not $ foldr mbExi f v
    n_common = do
      wd_token "no"; wd_token "common"; (q, f, v) <- possess
      return $ q . Not $ foldr mbExi (Tag DIG f) v
      -- take a closer look at this later.. why is (Tag DIG) *inside* important?


--- predicat parsing

predicat p = (wd_token "not" >> negative) <|> positive
  where
    positive = do (q, f) <- p term; return $ q . Tag DIG $ f
    negative = do (q, f) <- p term; return $ q . Tag DIG . Not $ f

m_predicat p = (wd_token "not" >> m_negative) <|> m_positive
  where
    m_positive = (wd_token "pairwise" >> p_positive) <|> s_positive
    -- we distinguish between *separate* and *pairwise*
    s_positive = do (q, f) <- p term; return $ q . Tag DMS $ f
    p_positive = do (q, f) <- p term; return $ q . Tag DMP $ f

    m_negative = (wd_token "pairwise" >> p_negative) <|> s_negative
    s_negative = do (q, f) <- p term; return $ q . Tag DMS . Not $ f
    p_negative = do (q, f) <- p term; return $ q . Tag DMP . Not $ f




--- notions

basentn = liftM digadd $ cm <|> sym_eqnt <|> (set </> prim_ntn term)
  where
    cm       = wd_token "common" >> prim_cm_ntn term terms
    sym_eqnt = do
      t <- lexicalCheck isTrm s_term
      v <- hidden; return (id, zEqu zHole t, [v])

sym_notion  =  (paren (prim_snt s_term) </> prim_tvr) >>= (digntn . digadd)


gnotion nt ra = do
  ls <- liftM reverse la; (q, f, vs) <- nt;
  rs <- opt [] $ liftM (:[]) $ ra <|> rc
  -- we can use <|> here because every ra in use begins with "such"
  return (q, foldr1 And $ f : ls ++ rs, vs)
  where
    la  = opt [] $ liftM2 (:) lc la
    lc  = predicat prim_un_adj </> m_predicat prim_m_un_adj
    rc  = (that >> conj_chain does_predicat <?> "that clause") <|> conj_chain is_predicat


anotion =
  art >> (gnotion basentn rat <?> "notion (at most one name)") >>= single >>= hol
  where
    hol (q, f, v) = return (q, subst zHole v f)
    rat = liftM (Tag DIG) stattr ---- why here Tag DIG??

notion  = label "notion" $ gnotion (basentn </> sym_notion) stattr >>= digntn

possess = gnotion (prim_of_ntn term) stattr >>= digntn


stattr  =  such >> that >> statement

digadd (q, f, v)  = (q, Tag DIG f, v)

digntn (q, f, v)  = dig f (map zVar v) >>= \ g -> return (q, g, v)

single (q, f, [v])  = return (q, f, v)
single _            = fail "inadmissible multinamed notion"

--- terms

terms = label "terms" $
  liftM (foldl1 fld) $ m_term `sepBy` comma
  where
    m_term     = qu_notion -|- liftM s2m definite_term
    s2m (q, t) = (q, [t])

    fld (q, ts) (r, ss) = (q . r, ts ++ ss)

term = label "a term" $ (qu_notion >>= m2s) -|- definite_term
  where
    m2s (q, [t]) = return (q, t)
    m2s _ = fail "inadmissible multinamed notion"


qu_notion = label "quantified notion" $
  paren (fa <|> ex <|> no)
  where
    fa = do
      wd_tokenOf ["every", "each", "all", "any"]; (q, f, v) <- notion
      return (q . flip (foldr zAll) v . blImp f, map zVar v)

    ex = do
      wd_token "some"; (q, f, v) <- notion
      return (q . flip (foldr zExi) v . blAnd f, map zVar v)

    no = do
      wd_token "no"; (q, f, v) <- notion
      return (q . flip (foldr zAll) v . blImp f . Not, map zVar v)


definite_term = symbolic_term -|- definite_noun
  where
    definite_noun = paren (art >> prim_fun term)

plain_term = symbolic_term -|- plain_definite_noun
  where
    plain_definite_noun = paren (art >> prim_fun plain_term)

symbolic_term = liftM ((,) id) s_term


--- symbolic notation


s_form  = s_iff
  where
    s_iff = s_imp >>= bin_f Iff (symbol "<=>" >> s_imp)
    s_imp = s_dis >>= bin_f Imp (symbol "=>"  >> s_imp)
    s_dis = s_con >>= bin_f Or  (symbol "\\/" >> s_dis)
    s_con = s_una >>= bin_f And (symbol "/\\" >> s_con)
    s_una = s_all -|- s_exi -|- s_not -|- s_dot -|- s_atm
    s_all = liftM2 (qua_f zAll Imp) (wd_token "forall" >> sym_notion) s_una
    s_exi = liftM2 (qua_f zExi And) (wd_token "exists" >> sym_notion) s_una
    s_not = liftM Not $ wd_token "not" >> s_una
    s_dot = wd_token ":" >> s_form
    s_atm = s_atom

    qua_f qu op (_, f, v) = flip (foldr qu) v . op f

    bin_f op p f = optLL1 f $ liftM (op f) p


s_atom = s_relation -|- expar statement
  where
    s_relation = s_chain </> prim_cpr s_term

    s_chain = liftM (foldl1 And . concat) s_hd

    s_hd  = l_hd -|- (s_ts >>= s_tl)
    l_hd  = do
      pr <- prim_lpr s_term; rs <- s_ts
      liftM (map pr rs :) $ opt [] $ s_tl rs

    s_tl ls = i_tl ls -|- r_tl ls
    i_tl ls = do
      pr <- prim_ipr s_term; rs <- s_ts
      liftM (liftM2 pr ls rs :) $ opt [] $ s_tl rs
    r_tl ls = do pr <- prim_rpr s_term; return [map pr ls]

    s_ts = s_term `sepBy` wd_token ","


s_term = i_term
  where
    i_term  = l_term >>= i_tl
    i_tl t  = opt t $ (prim_ifn s_term `ap` return t `ap` i_term) >>= i_tl -- I'm pretty sure this second i_tl can never succeed... test this later

    l_term  = r_term -|- (prim_lfn s_term `ap` l_term)

    r_term  = c_term >>= r_tl
    r_tl t  = opt t $ (prim_rfn s_term `ap` return t) >>= r_tl

    c_term  = s_var -|- expar s_term -|- prim_cfn s_term

s_var = liftM zVar var

-- class term equations

classEq = twoClassTerms </> oneClassTerm
  where
    twoClassTerms = do
      cnd1 <- liftM stripSet symb_set_notation; sm_token "="
      cnd2 <- liftM stripSet symb_set_notation; h <- hidden
      return $ zAll h $ Iff (cnd1 $ zVar h) (cnd2 $ zVar h)
    stripSet = (.) strip . fst

    oneClassTerm = left </> right
    left = do
      cnd <- liftM stripSet symb_set_notation; sm_token "="
      t   <- s_term; h <- hidden; let hv = zVar h
      return $ zAll h $ Iff (cnd hv) (zElem hv t)
    right = do
      t   <- s_term; sm_token "="; h <- hidden; let hv = zVar h
      cnd <- liftM stripSet symb_set_notation
      return $ zAll h $ Iff (zElem hv t) (cnd hv)




-- selection

selection = liftM (foldl1 And) $ (art >> takeLongest namedNotion) `sepByLL1` comma
  where
    namedNotion = label "named notion" $ do
      (q, f, vs) <- notion; guard (all isExplicitName vs); return $ q f
    isExplicitName ('x':_) = True; isExplicitName _ = False


-- function and set syntax

-- -- sets
setNotion = do
  v <- after var (sm_token "="); (_, f, _) <- set
  dig (Tag DIG f) [zVar v]

set = symb_set <|> set_of
  where
    set_of   = do
      wd_tokenOf ["set", "sets"]; nm <- var -|- hidden; wd_token "of";
      (q, f, u) <- notion >>= single; vnm <- hidden;
      return (id, setForm vnm $ subst (zVar vnm) u $ q f, [nm])
    symb_set = do
      (cnd, nm) <- symb_set_notation; h <- hidden
      return (id, setForm nm $ cnd $ zVar nm, [h])
    setForm nm = And (zSet zHole) . zAll nm . Iff (zElem (zVar nm) zHole)


symb_set_notation = cndSet </> finSet
  where
    finSet = exbrc $ do
      ts <- s_term `sepByLL1` sm_token ","; h <- hidden
      return (\tr -> foldr1 Or $ map (zEqu tr) ts, h)
    cndSet = exbrc $ do
      (tag, c, t) <- sepFrom; st <- sm_token "|" >> statement;
      vs <- freeVars t; nm <- if isVar t then return $ trName t else hidden
      return (\tr -> tag $ c tr `blAnd` mbEqu vs tr t st, nm)

    mbEqu _ tr Var{trName = v} = subst tr v
    mbEqu vs tr t = \st -> foldr mbExi (st `And` zEqu tr t) vs


sepFrom = ntnSep -|- setSep -|- noSep
  where
    ntnSep = do
      (q, f, v) <- notion >>= single; guard (not . isEqu $ f)
      return (Tag DRP, \tr -> subst tr v $ q f, zVar v)
    setSep = do
      t <- s_term; cnd <- wd_token "in" >> elementCnd
      return (id, cnd, t)
    noSep  = do
      t <- s_term; return (Tag DRP, const Top, t)

elementCnd = setTerm </> liftM fst symb_set_notation
  where
    setTerm = s_term >>= return . flip zElem

-- -- functions

functionNotion = liftM2 (&) s_var $ wordFun <|> (sm_token "=" >> lambda)
  where
  wordFun = do
    sm_token "["; t <- pair; sm_token "]"; sm_token "="; vs <- freeVars t
    def <- addDecl vs ld_body; (_, _, dom) <- wd_token "for" >> ld_in;
    let body = \f -> foldr zAll (Imp (t `zElem` zDom f) $ def $ zApp f t) vs
    return $ \f -> zFun f `And` Tag DDM (dom f) `And` (body f)

ld_body = paren $  cases <|> chooseInTerm

cases = do
  cas <- ld_case `sepByLL1` sm_token ","
  return $ \fx -> foldr1 And $ map ((&) fx) cas
  where
    ld_case = do
      optLL1 () $ wd_token "case"; condition <- statement; arrow
      liftM ((.) $ Tag DCD . Imp condition) chooseInTerm

chooseInTerm = do
  chs <- optLL1 [] $ after (ld_choice `sepByLL1` sm_token ",") (wd_token "in")
  f   <- term -|- defTerm; return $ flip (foldr ($)) chs . f
  where
    ld_choice = chc <|> def
    chc = do
      wd_token "choose"; (q, f, vs) <- art >> notion
      return $ flip (foldr zExi) vs . And (q f)
    def = do
      wd_token "define"; x <- var; sm_token "="
      ap <- ld_set <|> lambda
      return $ zExi x . And (Tag DEF $ ap $ zVar x)

    term    = liftM ((.) (Tag DEV) . flip zEqu) s_term
    defTerm = do
      ap <- ld_set <|> lambda; h <- hidden; let hv = zVar h
      return $ \fx -> zExi h $ And (Tag DEF $ ap hv) (Tag DEV $ zEqu fx hv)

    ld_set = do (_, t, _) <- set; return $ flip substH t


lambda = do
  (t, df_head, dom) <- ld_head; vs <- freeVars t; df <- addDecl vs ld_body
  return $ \f -> zFun f `And` Tag DDM (dom f) `And` (df_head f $ df $ zApp f t)
  where
    ld_head = dot $ sm_token "\\" >> ld_in

pair = s_var </> pr
  where
    pr = do [l,r] <- sm_patt pair pairPattern; return $ zPair l r
    pairPattern = [Sm "(", Vr, Sm ",", Vr, Sm ")"]

ld_in = do
  t <- pair; vs <- freeVars t; wd_token "in"; dom <- ld_dom;
  let df_head = \f -> foldr ((.) . zAll) (Imp (t `zElem` zDom f)) vs
  return (t, df_head, \f -> dom f t vs)
  where
    ld_dom = trm <|> setTrm
    trm    = do
      t <- s_term; return $ \f _ _ -> zDom f `zEqu` t
    setTrm = do
      (ap, _) <- symb_set_notation
      return $ \f t vs -> foldr zAll (Iff (t `zElem` zDom f) (ap t)) vs

---- chain tools

multExi ((q, f, vs):ns) = foldr mbExi (q f `blAnd` multExi ns) vs
multExi [] = Top

conj_chain = liftM (foldl1 And) . flip sepBy (wd_token "and")

qu_chain  = liftM (foldl fld id) $ wd_token "for" >> qu_notion `sepByLL1` comma -- we can use LL1 here, since there must always follow
  where                                                                       -- a parser belonging to the same non-terminal
    fld x (y, _)  = x . y


-- Digger

dig f [_] | occursS f  = fail "too few subjects for an m-predicate"
dig f ts  = return (dive f)
  where
    dive (Tag DIG f)  = down (digS) f
    dive (Tag DMS f)  = down (digM $ zip ts $ tail ts) f
    dive (Tag DMP f)  = down (digM $ pairMP ts) f
    dive f  | isTrm f = f
    dive f  = mapF dive f

    down fn (And f g) = And (down fn f) (down fn g)
    down fn f         = foldl1 And (fn f)

    digS f  | occursH f = map (\ x -> substH x f) ts
            | otherwise = [f]

    digM ps f | not (occursS f) = digS f
              | not (occursH f) = map (\ y -> substS y f) $ tail ts
              | otherwise = map (\ (x,y) -> substS y $ substH x f) ps

    pairMP (t:ts) = [ (t, s) | s <- ts ] ++ pairMP ts
    pairMP _      = []
