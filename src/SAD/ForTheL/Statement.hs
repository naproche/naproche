{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Syntax of ForThel statements.
-}



module SAD.ForTheL.Statement (
  statement,
  var, sVar, sTerm,
  anotion, dig, selection, setNotion, functionNotion) where

import SAD.ForTheL.Base
import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Parser.Primitives

import SAD.Parser.Token

import SAD.Data.Formula


import Debug.Trace
import qualified Control.Monad.State.Class as MS
import Data.Function ((&))


import Control.Monad

statement = headed <|> chained

headed = quStatem <|> ifThenStatem <|> wrongStatem
  where
    quStatem = liftM2 ($) quChain statement
    ifThenStatem =
      liftM2 Imp (wdToken "if" >> statement) (wdToken "then" >> statement)
    wrongStatem =
      mapM_ wdToken ["it", "is", "wrong", "that"] >> fmap Not statement



chained = label "chained statement" $ andOr <|> neitherNor >>= chainEnd
  where
    andOr = atomic >>= \f -> opt f (andChain f <|> orChain f)
    andChain f =
      fmap (foldl And f) $ wdToken "and" >> atomic `sepBy` wdToken "and"
    -- we take sepBy here instead of sepByLLx since we do not  know if the
    -- and/or wdToken binds to this statement or to an ambient one
    orChain f = fmap (foldl Or f) $ wdToken "or" >> atomic `sepBy` wdToken "or"

    neitherNor = do
      wdToken "neither"; f <- atomic; wdToken "nor"
      fs <- atomic `sepBy` wdToken "nor"
      return $ foldl1 And $ map Not (f:fs)


chainEnd f = optLL1 f $ and_st <|> or_st <|> iff_st <|> where_st
  where
    and_st = fmap (And f) $ wdToken "and" >> headed
    or_st = fmap (Or f) $ wdToken "or" >> headed
    iff_st = fmap (Iff f) $ iff >> statement
    where_st = do
      wdTokenOf ["when", "where"]; y <- statement
      return $ foldr zAll (Imp y f) (decl [] y)


atomic = label "atomic statement"
  thereIs <|> (simple </> (wehve >> smForm <|> thesis))
  where
    wehve = optLL1 () $ wdToken "we" >> wdToken "have"

thesis = art >> (thes <|> contrary <|> contradiction)
  where
    thes = wdToken "thesis" >> return zThesis
    contrary = wdToken "contrary" >> return (Not zThesis)
    contradiction = wdToken "contradiction" >> return Bot

thereIs = there >> (noNotion -|- notions)
  where
    noNotion = do 
      wdToken "no"; (q, f, vs) <- notion;
      return $ Not $ foldr mbExi (q f) vs
    notions = fmap multExi $ art >> notion `sepBy` comma




simple = label "simple statement" $ do
  (q, ts) <- terms; p <- conjChain doesPredicat;
  q' <- optLL1 id quChain;
  -- this part is not in the language description
  -- example: x = y *for every real number x*.
  q . q' <$> dig p ts

smForm = liftM2 (flip ($)) (sForm -|- classEq) $ optLL1 id quChain

--- predicates


doesPredicat = label "does predicat" $
  (does >> (doP -|- multiDoP)) <|> hasP <|> isChain
  where
    doP = predicat primVer
    multiDoP = mPredicat primMultiVer
    hasP = has >> hasPredicate
    isChain = is  >> conjChain (isAPredicat -|- isPredicat)


isPredicat = label "is predicat" $
  pAdj -|- pMultiAdj -|- (with >> hasPredicate)
  where
    pAdj = predicat primAdj
    pMultiAdj = mPredicat primMultiAdj


isAPredicat = label "isA predicat" $ notNtn <|> ntn
  -- Unlike the langugae description, we distinguish positive and negative
  -- rather than notions and fixed terms
  where
    ntn = fmap (uncurry ($)) anotion
    notNtn = do
      wdToken "not"; (q, f) <- anotion; let unfinished = dig f [zHole]
      optLLx (q $ Not f) $ fmap (q. Tag Dig . Not) unfinished

hasPredicate = label "has predicat" $ noPossessive <|> possessive
  where
    possessive = art >> common <|> unary
    unary = fmap (Tag Dig . multExi) $ possess `sepBy` (comma >> art)
    common = wdToken "common" >> fmap multExi (fmap digadd possess `sepBy` comma)

    noPossessive = nUnary -|- nCommon
    nUnary = do
      wdToken "no"; (q, f, v) <- possess;
      return $ q . Tag Dig . Not $ foldr mbExi f v
    nCommon = do
      wdToken "no"; wdToken "common"; (q, f, v) <- possess
      return $ q . Not $ foldr mbExi (Tag Dig f) v
      -- take a closer look at this later.. why is (Tag Dig) *inside* important?


--- predicat parsing

predicat p = (wdToken "not" >> negative) <|> positive
  where
    positive = do (q, f) <- p term; return $ q . Tag Dig $ f
    negative = do (q, f) <- p term; return $ q . Tag Dig . Not $ f

mPredicat p = (wdToken "not" >> mNegative) <|> mPositive
  where
    mPositive = (wdToken "pairwise" >> pPositive) <|> sPositive
    -- we distinguish between *separate* and *pairwise*
    sPositive = do (q, f) <- p term; return $ q . Tag DigMultiSubject $ f
    pPositive = do (q, f) <- p term; return $ q . Tag DigMultiPairwise $ f

    mNegative = (wdToken "pairwise" >> pNegative) <|> sNegative
    sNegative = do (q, f) <- p term; return $ q . Tag DigMultiSubject . Not $ f
    pNegative = do (q, f) <- p term; return $ q . Tag DigMultiPairwise . Not $ f




--- notions

basentn = fmap digadd $ cm <|> symEqnt <|> (set </> primNtn term)
  where
    cm = wdToken "common" >> primCmNtn term terms
    symEqnt = do
      t <- lexicalCheck isTrm sTerm
      v <- hidden; return (id, zEqu zHole t, [v])

symNotion = (paren (primSnt sTerm) </> primTvr) >>= (digntn . digadd)


gnotion nt ra = do
  ls <- fmap reverse la; (q, f, vs) <- nt;
  rs <- opt [] $ fmap (:[]) $ ra <|> rc
  -- we can use <|> here because every ra in use begins with "such"
  return (q, foldr1 And $ f : ls ++ rs, vs)
  where
    la = opt [] $ liftM2 (:) lc la
    lc = predicat primUnAdj </> mPredicat primMultiUnAdj
    rc = (that >> conjChain doesPredicat <?> "that clause") <|>
      conjChain isPredicat


anotion =
  art >> (gnotion basentn rat <?> "notion (at most one name)") >>=
  single >>= hol
  where
    hol (q, f, v) = return (q, subst zHole v f)
    rat = fmap (Tag Dig) stattr

notion = label "notion" $ gnotion (basentn </> symNotion) stattr >>= digntn

possess = gnotion (primOfNtn term) stattr >>= digntn


stattr = such >> that >> statement

digadd (q, f, v)  = (q, Tag Dig f, v)

digntn (q, f, v)  = dig f (map zVar v) >>= \ g -> return (q, g, v)

single (q, f, [v])  = return (q, f, v)
single _            = fail "inadmissible multinamed notion"

--- terms

terms = label "terms" $
  fmap (foldl1 fld) $ m_term `sepBy` comma
  where
    m_term     = quNotion -|- fmap s2m definiteTerm
    s2m (q, t) = (q, [t])

    fld (q, ts) (r, ss) = (q . r, ts ++ ss)

term = label "a term" $ (quNotion >>= m2s) -|- definiteTerm
  where
    m2s (q, [t]) = return (q, t)
    m2s _ = fail "inadmissible multinamed notion"


quNotion = label "quantified notion" $
  paren (fa <|> ex <|> no)
  where
    fa = do
      wdTokenOf ["every", "each", "all", "any"]; (q, f, v) <- notion
      return (q . flip (foldr zAll) v . blImp f, map zVar v)

    ex = do
      wdToken "some"; (q, f, v) <- notion
      return (q . flip (foldr zExi) v . blAnd f, map zVar v)

    no = do
      wdToken "no"; (q, f, v) <- notion
      return (q . flip (foldr zAll) v . blImp f . Not, map zVar v)


definiteTerm = symbolicTerm -|- definiteNoun
  where
    definiteNoun = paren (art >> primFun term)

plainTerm = symbolicTerm -|- plainDefiniteNoun
  where
    plainDefiniteNoun = paren (art >> primFun plainTerm)

symbolicTerm = fmap ((,) id) sTerm


--- symbolic notation


sForm  = sIff
  where
    sIff = sImp >>= binF Iff (symbol "<=>" >> sImp)
    sImp = sDis >>= binF Imp (symbol "=>"  >> sImp)
    sDis = sCon >>= binF Or  (symbol "\\/" >> sDis)
    sCon = sUna >>= binF And (symbol "/\\" >> sCon)
    sUna = sAll -|- sExi -|- sNot -|- sDot -|- sAtm
    sAll = liftM2 (quaF zAll Imp) (wdToken "forall" >> symNotion) sUna
    sExi = liftM2 (quaF zExi And) (wdToken "exists" >> symNotion) sUna
    sNot = fmap Not $ wdToken "not" >> sUna
    sDot = wdToken ":" >> sForm
    sAtm = sAtom

    quaF qu op (_, f, v) = flip (foldr qu) v . op f

    binF op p f = optLL1 f $ fmap (op f) p


sAtom = sRelation -|- expar statement
  where
    sRelation = sChain </> primCpr sTerm

    sChain = fmap (foldl1 And . concat) sHd

    sHd  = lHd -|- (sTs >>= sTl)
    lHd  = do
      pr <- primLpr sTerm; rs <- sTs
      fmap (map pr rs :) $ opt [] $ sTl rs

    sTl ls = iTl ls -|- rTl ls
    iTl ls = do
      pr <- primIpr sTerm; rs <- sTs
      fmap (liftM2 pr ls rs :) $ opt [] $ sTl rs
    rTl ls = do pr <- primRpr sTerm; return [map pr ls]

    sTs = sTerm `sepBy` wdToken ","


sTerm = iTerm
  where
    iTerm = lTerm >>= iTl
    iTl t = opt t $ (primIfn sTerm `ap` return t `ap` iTerm) >>= iTl

    lTerm = rTerm -|- (primLfn sTerm `ap` lTerm)

    rTerm = cTerm >>= rTl
    rTl t = opt t $ (primRfn sTerm `ap` return t) >>= rTl

    cTerm = sVar -|- expar sTerm -|- primCfn sTerm

sVar = fmap zVar var

-- class term equations

classEq = twoClassTerms </> oneClassTerm
  where
    twoClassTerms = do
      cnd1 <- fmap stripSet symbSetNotation; smTokenOf "="
      cnd2 <- fmap stripSet symbSetNotation; h <- hidden
      return $ zAll h $ Iff (cnd1 $ zVar h) (cnd2 $ zVar h)
    stripSet = (.) strip . fst

    oneClassTerm = left </> right
    left = do
      cnd <- fmap stripSet symbSetNotation; smTokenOf "="
      t <- sTerm; h <- hidden; let hv = zVar h
      return $ zAll h $ Iff (cnd hv) (zElem hv t)
    right = do
      t <- sTerm; smTokenOf "="; h <- hidden; let hv = zVar h
      cnd <- fmap stripSet symbSetNotation
      return $ zAll h $ Iff (zElem hv t) (cnd hv)




-- selection

selection = fmap (foldl1 And) $ (art >> takeLongest namedNotion) `sepByLL1` comma
  where
    namedNotion = label "named notion" $ do
      (q, f, vs) <- notion; guard (all isExplicitName vs); return $ q f
    isExplicitName ('x':_) = True; isExplicitName _ = False


-- function and set syntax

-- -- sets
setNotion = do
  v <- after var (smTokenOf "="); (_, f, _) <- set
  dig (Tag Dig f) [zVar v]

set = symbSet <|> setOf
  where
    setOf = do
      wdTokenOf ["set", "sets"]; nm <- var -|- hidden; wdToken "of";
      (q, f, u) <- notion >>= single; vnm <- hidden;
      return (id, setForm vnm $ subst (zVar vnm) u $ q f, [nm])
    symbSet = do
      (cnd, nm) <- symbSetNotation; h <- hidden
      return (id, setForm nm $ cnd $ zVar nm, [h])
    setForm nm = And (zSet zHole) . zAll nm . Iff (zElem (zVar nm) zHole)


symbSetNotation = cndSet </> finSet
  where
    finSet = exbrc $ do
      ts <- sTerm `sepByLL1` smTokenOf ","; h <- hidden
      return (\tr -> foldr1 Or $ map (zEqu tr) ts, h)
    cndSet = exbrc $ do
      (tag, c, t) <- sepFrom; st <- smTokenOf "|" >> statement;
      vs <- freeVars t; nm <- if isVar t then return $ trName t else hidden
      return (\tr -> tag $ c tr `blAnd` mbEqu vs tr t st, nm)

    mbEqu _ tr Var{trName = v} = subst tr v
    mbEqu vs tr t = \st -> foldr mbExi (st `And` zEqu tr t) vs


sepFrom = ntnSep -|- setSep -|- noSep
  where
    ntnSep = do
      (q, f, v) <- notion >>= single; guard (not . isEquality $ f)
      return (Tag Replacement, \tr -> subst tr v $ q f, zVar v)
    setSep = do
      t <- sTerm; cnd <- wdToken "in" >> elementCnd
      return (id, cnd, t)
    noSep  = do
      t <- sTerm; return (Tag Replacement, const Top, t)

elementCnd = setTerm </> fmap fst symbSetNotation
  where
    setTerm = sTerm >>= return . flip zElem

-- -- functions

functionNotion = liftM2 (&) sVar $ wordFun <|> (smTokenOf "=" >> lambda)
  where
  wordFun = do
    smTokenOf "["; t <- pair; smTokenOf "]"; smTokenOf "="; vs <- freeVars t
    def <- addDecl vs lambdaBody; (_, _, dom) <- wdToken "for" >> lambdaIn;
    let body f = foldr zAll (Imp (t `zElem` zDom f) $ def $ zApp f t) vs
    return $ \f -> zFun f `And` Tag Domain (dom f) `And` body f

lambdaBody = paren $ cases <|> chooseInTerm

cases = do
  cas <- ld_case `sepByLL1` smTokenOf ","
  return $ \fx -> foldr1 And $ map ((&) fx) cas
  where
    ld_case = do
      optLL1 () $ wdToken "case"; condition <- statement; arrow
      fmap ((.) $ Tag Condition . Imp condition) chooseInTerm

chooseInTerm = do
  chs <- optLL1 [] $ after (ld_choice `sepByLL1` smTokenOf ",") (wdToken "in")
  f   <- term -|- defTerm; return $ flip (foldr ($)) chs . f
  where
    ld_choice = chc <|> def
    chc = do
      wdToken "choose"; (q, f, vs) <- art >> notion
      return $ flip (foldr zExi) vs . And (q f)
    def = do
      wdToken "define"; x <- var; smTokenOf "="
      ap <- ld_set <|> lambda
      return $ zExi x . And (Tag Defined $ ap $ zVar x)

    term = fmap ((.) (Tag Evaluation) . flip zEqu) sTerm
    defTerm = do
      ap <- ld_set <|> lambda; h <- hidden; let hv = zVar h
      return $ \fx -> zExi h $ And (Tag Defined $ ap hv) (Tag Evaluation $ zEqu fx hv)

    ld_set = do (_, t, _) <- set; return $ flip substHole t


lambda = do
  (t, df_head, dom) <- ld_head; vs <- freeVars t; df <- addDecl vs lambdaBody
  return $ \f -> zFun f `And` Tag Domain (dom f) `And` (df_head f $ df $ zApp f t)
  where
    ld_head = dot $ smTokenOf "\\" >> lambdaIn

pair = sVar </> pr
  where
    pr = do [l,r] <- smPatt pair pairPattern; return $ zPair l r
    pairPattern = [Sm "(", Vr, Sm ",", Vr, Sm ")"]

lambdaIn = do
  t <- pair; vs <- freeVars t; wdToken "in"; dom <- ld_dom;
  let df_head f = foldr ((.) . zAll) (Imp (t `zElem` zDom f)) vs
  return (t, df_head, \f -> dom f t vs)
  where
    ld_dom = trm <|> setTrm
    trm = do
      t <- sTerm; return $ \f _ _ -> zDom f `zEqu` t
    setTrm = do
      (ap, _) <- symbSetNotation
      return $ \f t vs -> foldr zAll (Iff (t `zElem` zDom f) (ap t)) vs

---- chain tools

multExi ((q, f, vs):ns) = foldr mbExi (q f `blAnd` multExi ns) vs
multExi [] = Top

conjChain = fmap (foldl1 And) . flip sepBy (wdToken "and")

quChain = fmap (foldl fld id) $ wdToken "for" >> quNotion `sepByLL1` comma
-- we can use LL1 here, since there must always follow a parser belonging to the
-- same non-terminal
  where
    fld x (y, _) = x . y


-- Digger

dig f [_] | occursS f = fail "too few subjects for an m-predicate"
dig f ts = return (dive f)
  where
    dive (Tag Dig f)  = down (digS) f
    dive (Tag DigMultiSubject f) = down (digM $ zip ts $ tail ts) f
    dive (Tag DigMultiPairwise f) = down (digM $ pairMP ts) f
    dive f | isTrm f = f
    dive f = mapF dive f

    down fn (And f g) = And (down fn f) (down fn g)
    down fn f = foldl1 And (fn f)

    digS f
      | occursH f = map (\ x -> substHole x f) ts
      | otherwise = [f]

    digM ps f
      | not (occursS f) = digS f
      | not (occursH f) = map (\ y -> substSlot y f) $ tail ts
      | otherwise = map (\ (x,y) -> substSlot y $ substHole x f) ps

    pairMP (t:ts) = [ (t, s) | s <- ts ] ++ pairMP ts
    pairMP _ = []
