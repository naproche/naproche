{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Syntax of ForThel statements.
-}



module SAD.ForTheL.Statement (
  statement,
  var, sVar, sTerm,
  anotion, dig, selection, setNotion, functionNotion, plainTerm) where

import SAD.ForTheL.Base
import SAD.ForTheL.Reports (markupToken, markupTokenOf)
import qualified SAD.ForTheL.Reports as Reports
import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Parser.Primitives

import SAD.Data.Formula
import SAD.Core.SourcePos
import qualified SAD.Data.Text.Decl as Decl

import Data.Function ((&))


import Control.Applicative
import Control.Monad


statement :: FTL Formula
statement = headed <|> chained

headed :: FTL Formula
headed = quStatem <|> ifThenStatem <|> wrongStatem
  where
    quStatem = liftM2 ($) quChain statement
    ifThenStatem = liftM2 Imp
      (markupToken Reports.ifThen "if" >> statement)
      (markupToken Reports.ifThen "then" >> statement)
    wrongStatem =
      mapM_ token' ["it", "is", "wrong", "that"] >> fmap Not statement



chained :: FTL Formula
chained = label "chained statement" $ andOr <|> neitherNor >>= chainEnd
  where
    andOr = atomic >>= \f -> opt f (andChain f <|> orChain f)
    andChain f =
      fmap (foldl And f) $ and >> atomic `sepBy` and
    -- we take sepBy here instead of sepByLLx since we do not  know if the
    -- and/or token' binds to this statement or to an ambient one
    orChain f = fmap (foldl Or f) $ or >> atomic `sepBy`or
    and = markupToken Reports.conjunctiveAnd "and"
    or = markupToken Reports.or "or"

    neitherNor = do
      markupToken Reports.neitherNor "neither"; f <- atomic
      markupToken Reports.neitherNor "nor"
      fs <- atomic `sepBy` markupToken Reports.neitherNor "nor"
      return $ foldl1 And $ map Not (f:fs)


chainEnd :: Formula -> FTL Formula
chainEnd f = optLL1 f $ and_st <|> or_st <|> iff_st <|> where_st
  where
    and_st = fmap (And f) $ markupToken Reports.conjunctiveAnd "and" >> headed
    or_st = fmap (Or f) $ markupToken Reports.or "or" >> headed
    iff_st = fmap (Iff f) $ iff >> statement
    where_st = do
      markupTokenOf Reports.whenWhere ["when", "where"]; y <- statement
      return $ foldr zAll (Imp y f) (declNames [] y)


atomic :: FTL Formula
atomic = label "atomic statement"
  thereIs <|> (simple </> (wehve >> smForm <|> thesis))
  where
    wehve = optLL1 () $ token' "we" >> token' "have"

thesis :: Parser st Formula
thesis = art >> (thes <|> contrary <|> contradiction)
  where
    thes = token' "thesis" >> return zThesis
    contrary = token' "contrary" >> return (Not zThesis)
    contradiction = token' "contradiction" >> return Bot

thereIs :: FTL Formula
thereIs = label "there-is statement" $ there >> (noNotion -|- notions)
  where
    noNotion = label "no-notion" $ do
      token' "no"; (q, f, vs) <- declared notion;
      return $ Not $ foldr mbdExi (q f) vs
    notions = fmap multExi $ art >> declared notion `sepBy` comma




simple :: FTL Formula
simple = label "simple statement" $ do
  (q, ts) <- terms; p <- conjChain doesPredicate;
  q' <- optLL1 id quChain;
  -- this part is not in the language description
  -- example: x = y *for every real number x*.
  q . q' <$> dig p ts

smForm :: FTL Formula
smForm = liftM2 (flip ($)) (sForm -|- classEq) $ optLL1 id quChain

--- predicates


doesPredicate :: FTL Formula
doesPredicate = label "does predicate" $
  (does >> (doP -|- multiDoP)) <|> hasP <|> isChain
  where
    doP = predicate primVer
    multiDoP = mPredicate primMultiVer
    hasP = has >> hasPredicate
    isChain = is  >> conjChain (isAPredicat -|- isPredicate)


isPredicate :: FTL Formula
isPredicate = label "is predicate" $
  pAdj -|- pMultiAdj -|- (with >> hasPredicate)
  where
    pAdj = predicate primAdj
    pMultiAdj = mPredicate primMultiAdj


isAPredicat :: FTL Formula
isAPredicat = label "isA predicate" $ notNtn <|> ntn
  -- Unlike the langugae description, we distinguish positive and negative
  -- rather than notions and fixed terms
  where
    ntn = fmap (uncurry ($)) anotion
    notNtn = do
      token' "not"; (q, f) <- anotion; let unfinished = dig f [zHole]
      optLLx (q $ Not f) $ fmap (q. Tag Dig . Not) unfinished

hasPredicate :: FTL Formula
hasPredicate = label "has predicate" $ noPossessive <|> possessive
  where
    possessive = art >> common <|> unary
    unary = fmap (Tag Dig . multExi) $ declared possess `sepBy` (comma >> art)
    common = token' "common" >>
      fmap multExi (fmap digadd (declared possess) `sepBy` comma)

    noPossessive = nUnary -|- nCommon
    nUnary = do
      token' "no"; (q, f, v) <- declared possess;
      return $ q . Tag Dig . Not $ foldr mbdExi f v
    nCommon = do
      token' "no"; token' "common"; (q, f, v) <- declared possess
      return $ q . Not $ foldr mbdExi (Tag Dig f) v
      -- take a closer look at this later.. why is (Tag Dig) *inside* important?


--- predicate parsing

predicate :: (FTL UTerm -> FTL UTerm) -> FTL Formula
predicate p = (token' "not" >> negative) <|> positive
  where
    positive = do (q, f) <- p term; return $ q . Tag Dig $ f
    negative = do (q, f) <- p term; return $ q . Tag Dig . Not $ f

mPredicate :: (FTL UTerm -> FTL UTerm) -> FTL Formula
mPredicate p = (token' "not" >> mNegative) <|> mPositive
  where
    mPositive = (token' "pairwise" >> pPositive) <|> sPositive
    -- we distinguish between *separate* and *pairwise*
    sPositive = do (q, f) <- p term; return $ q . Tag DigMultiSubject $ f
    pPositive = do (q, f) <- p term; return $ q . Tag DigMultiPairwise $ f

    mNegative = (token' "pairwise" >> pNegative) <|> sNegative
    sNegative = do (q, f) <- p term; return $ q . Tag DigMultiSubject . Not $ f
    pNegative = do (q, f) <- p term; return $ q . Tag DigMultiPairwise . Not $ f




--- notions

basentn :: Parser
             FState (Formula -> Formula, Formula, [(String, SourcePos)])
basentn = fmap digadd $ cm <|> symEqnt <|> (set </> primNtn term)
  where
    cm = token' "common" >> primCmNtn term terms
    symEqnt = do
      t <- lexicalCheck isTrm sTerm
      v <- hidden; return (id, zEqu zHole t, [v])

symNotion :: Parser
               FState (Formula -> Formula, Formula, [(String, SourcePos)])
symNotion = (paren (primSnt sTerm) </> primTvr) >>= (digntn . digadd)


gnotion :: Parser
             FState (Formula -> Formula, Formula, [(String, SourcePos)])
           -> FTL Formula
           -> Parser
                FState (Formula -> Formula, Formula, [(String, SourcePos)])
gnotion nt ra = do
  ls <- fmap reverse la; (q, f, vs) <- nt;
  rs <- opt [] $ fmap (:[]) $ ra <|> rc
  -- we can use <|> here because every ra in use begins with "such"
  return (q, foldr1 And $ f : ls ++ rs, vs)
  where
    la = opt [] $ liftM2 (:) lc la
    lc = predicate primUnAdj </> mPredicate primMultiUnAdj
    rc = (that >> conjChain doesPredicate <?> "that clause") <|>
      conjChain isPredicate


anotion :: FTL (Formula -> Formula, Formula)
anotion = label "notion (at most one name)" $
  art >> gnotion basentn rat >>= single >>= hol
  where
    hol (q, f, v) = return (q, subst zHole (fst v) f)
    rat = fmap (Tag Dig) stattr

notion :: Parser
            FState (Formula -> Formula, Formula, [(String, SourcePos)])
notion = label "notion" $ gnotion (basentn </> symNotion) stattr >>= digntn

possess :: Parser
             FState (Formula -> Formula, Formula, [(String, SourcePos)])
possess = label "possesive notion" $ gnotion (primOfNtn term) stattr >>= digntn


stattr :: FTL Formula
stattr = label "such-that attribute" $ such >> that >> statement

digadd :: (a, Formula, c) -> (a, Formula, c)
digadd (q, f, v) = (q, Tag Dig f, v)

digntn :: Monad m =>
          (a, Formula, [(String, SourcePos)])
          -> m (a, Formula, [(String, SourcePos)])
digntn (q, f, v) = dig f (map pVar v) >>= \ g -> return (q, g, v)

single :: Monad m => (a, b, [c]) -> m (a, b, c)
single (q, f, [v]) = return (q, f, v)
single _ = fail "inadmissible multinamed notion"

--- terms

terms :: FTL (Formula -> Formula, [Formula])
terms = label "terms" $
  fmap (foldl1 fld) $ m_term `sepBy` comma
  where
    m_term = quNotion -|- fmap s2m definiteTerm
    s2m (q, t) = (q, [t])

    fld (q, ts) (r, ss) = (q . r, ts ++ ss)

term :: FTL UTerm
term = label "a term" $ (quNotion >>= m2s) -|- definiteTerm
  where
    m2s (q, [t]) = return (q, t)
    m2s _ = fail "inadmissible multinamed notion"


quNotion :: FTL (Formula -> Formula, [Formula])
quNotion = label "quantified notion" $
  paren (fa <|> ex <|> no)
  where
    fa = do
      tokenOf' ["every", "each", "all", "any"]; (q, f, v) <- notion
      vDecl <- mapM makeDecl v
      return (q . flip (foldr dAll) vDecl . blImp f, map pVar v)

    ex = do
      token' "some"; (q, f, v) <- notion
      vDecl <- mapM makeDecl v
      return (q . flip (foldr dExi) vDecl . blAnd f, map pVar v)

    no = do
      token' "no"; (q, f, v) <- notion
      vDecl<- mapM makeDecl v
      return (q . flip (foldr dAll) vDecl . blImp f . Not, map pVar v)


definiteTerm :: FTL (Formula -> Formula, Formula)
definiteTerm = label "definiteTerm" $  symbolicTerm -|- definiteNoun
  where
    definiteNoun = label "definiteNoun" $ paren (art >> primFun term)

plainTerm :: FTL (Formula -> Formula, Formula)
plainTerm = symbolicTerm -|- plainDefiniteNoun
  where
    plainDefiniteNoun = paren (art >> primFun plainTerm)

symbolicTerm :: FTL (a -> a, Formula)
symbolicTerm = fmap ((,) id) sTerm


--- symbolic notation


sForm :: FTL Formula
sForm  = sIff
  where
    sIff = sImp >>= binF Iff (symbol "<=>" >> sImp)
    sImp = sDis >>= binF Imp (symbol "=>"  >> sImp)
    sDis = sCon >>= binF Or  (symbol "\\/" >> sDis)
    sCon = sUna >>= binF And (symbol "/\\" >> sCon)
    sUna = sAll -|- sExi -|- sNot -|- sDot -|- sAtm
    sAll = liftM2 (quaF dAll Imp) (token' "forall" >> declared symNotion) sUna
    sExi = liftM2 (quaF dExi And) (token' "exists" >> declared symNotion) sUna
    sNot = fmap Not $ token' "not" >> sUna
    sDot = token' ":" >> sForm
    sAtm = sAtom

    quaF qu op (_, f, v) = flip (foldr qu) v . op f

    binF op p f = optLL1 f $ fmap (op f) p


sAtom :: FTL Formula
sAtom = sRelation -|- parenthesised statement
  where
    sRelation = sChain </> primCpr sTerm

    sChain = fmap (foldl1 And . concat) sHd

    sHd = lHd -|- (sTs >>= sTl)
    lHd = do
      pr <- primLpr sTerm; rs <- sTs
      fmap (map pr rs :) $ opt [] $ sTl rs

    sTl ls = iTl ls -|- rTl ls
    iTl ls = do
      pr <- primIpr sTerm; rs <- sTs
      fmap (liftM2 pr ls rs :) $ opt [] $ sTl rs
    rTl ls = do pr <- primRpr sTerm; return [map pr ls]

    sTs = sTerm `sepBy` token' ","


sTerm :: FTL Formula
sTerm = iTerm
  where
    iTerm = lTerm >>= iTl
    iTl t = opt t $ (primIfn sTerm `ap` return t `ap` iTerm) >>= iTl

    lTerm = rTerm -|- label "symbolic term" (primLfn sTerm `ap` lTerm)

    rTerm = cTerm >>= rTl
    rTl t = opt t $ (primRfn sTerm `ap` return t) >>= rTl

    cTerm = label "symbolic term" $ sVar -|- parenthesised sTerm -|- primCfn sTerm

sVar :: Parser st Formula
sVar = fmap pVar var

-- class term equations

classEq :: FTL Formula
classEq = twoClassTerms </> oneClassTerm
  where
    twoClassTerms = do
      cnd1 <- fmap stripSet symbSetNotation; token "="
      cnd2 <- fmap stripSet symbSetNotation; h <- hidden
      hDecl <- makeDecl h
      return $ dAll hDecl $ Iff (cnd1 $ pVar h) (cnd2 $ pVar h)
    stripSet = (.) strip . fst

    oneClassTerm = left </> right
    left = do
      cnd <- fmap stripSet symbSetNotation; token "="
      t <- sTerm; h <- hidden; hDecl <- makeDecl h; let hv = pVar h
      return $ All hDecl $ Iff (cnd hv) (zElem hv t)
    right = do
      t <- sTerm; token "="; h <- hidden; hDecl <- makeDecl h
      let hv = pVar h
      cnd <- fmap stripSet symbSetNotation
      return $ dAll hDecl $ Iff (zElem hv t) (cnd hv)




-- selection

selection :: FTL Formula
selection = fmap (foldl1 And) $ (art >> takeLongest namedNotion) `sepByLL1` comma
  where
    namedNotion = label "named notion" $ do
      (q, f, vs) <- notion; guard (all isExplicitName $ map fst vs); return $ q f
    isExplicitName ('x':_) = True; isExplicitName _ = False


-- function and set syntax

-- -- sets
setNotion :: FTL Formula
setNotion = do
  v <- after var (token "="); (_, f, _) <- set
  dig (Tag Dig f) [pVar v]

set :: FTL MNotion
set = label "set definition" $ symbSet <|> setOf
  where
    setOf = do
      tokenOf' ["set", "sets"]; nm <- var -|- hidden; token' "of";
      (q, f, u) <- notion >>= single; vnm <- hidden
      vnmDecl <- makeDecl vnm;
      return (id, setForm vnmDecl $ subst (pVar vnm) (fst u) $ q f, [nm])
    symbSet = do
      (cnd, nm) <- symbSetNotation; h <- hidden
      nmDecl <- makeDecl nm
      return (id, setForm nmDecl $ cnd $ pVar nm, [h])
    setForm dcl = let nm = (Decl.name dcl, Decl.position dcl) in
      And (zSet zHole) . dAll dcl . Iff (zElem (pVar nm) zHole)


symbSetNotation :: Parser
                     FState (Formula -> Formula, (String, SourcePos))
symbSetNotation = cndSet </> finSet
  where
    finSet = braced $ do
      ts <- sTerm `sepByLL1` token ","; h <- hidden
      return (\tr -> foldr1 Or $ map (zEqu tr) ts, h)
    cndSet = braced $ do
      (tag, c, t) <- sepFrom; st <- token "|" >> statement;
      vs <- freeVarPositions t; vsDecl <- mapM makeDecl vs;
      nm <- if isVar t then return $ (trName t, trPosition t) else hidden
      return (\tr -> tag $ c tr `blAnd` mbEqu vsDecl tr t st, nm)

    mbEqu _ tr Var{trName = v} = subst tr v
    mbEqu vs tr t = \st -> foldr mbdExi (st `And` zEqu tr t) vs


sepFrom :: Parser
             FState (Formula -> Formula, Formula -> Formula, Formula)
sepFrom = ntnSep -|- setSep -|- noSep
  where
    ntnSep = do
      (q, f, v) <- notion >>= single; guard (not . isEquality $ f)
      return (Tag Replacement, \tr -> subst tr (fst v) $ q f, pVar v)
    setSep = do
      t <- sTerm; cnd <- token' "in" >> elementCnd
      return (id, cnd, t)
    noSep  = do
      t <- sTerm; return (Tag Replacement, const Top, t)

elementCnd :: FTL (Formula -> Formula)
elementCnd = setTerm </> fmap fst symbSetNotation
  where
    setTerm = sTerm >>= return . flip zElem

-- -- functions

functionNotion :: FTL Formula
functionNotion = liftM2 (&) sVar $ wordFun <|> (token "=" >> lambda)
  where
  wordFun = do
    token "["; t <- pair; token "]"; token "="; vs <- freeVarPositions t
    def <- addDecl (map fst vs) lambdaBody; (_, _, dom) <- token' "for" >> lambdaIn;
    vsDecl <- mapM makeDecl vs
    let body f = foldr dAll (Imp (t `zElem` zDom f) $ def $ zApp f t) vsDecl
    return $ \f -> zFun f `And` Tag Domain (dom f) `And` body f

lambdaBody :: FTL (Formula -> Formula)
lambdaBody = label "function definition" $ paren $ cases <|> chooseInTerm

cases :: FTL (Formula -> Formula)
cases = do
  cas <- ld_case `sepByLL1` token ","
  return $ \fx -> foldr1 And $ map ((&) fx) cas
  where
    ld_case = do
      optLL1 () $ token' "case"; condition <- statement; arrow
      fmap ((.) $ Tag Condition . Imp condition) chooseInTerm

chooseInTerm :: FTL (Formula -> Formula)
chooseInTerm = do
  chs <- optLL1 [] $ after (ld_choice `sepByLL1` token ",") (token' "in")
  f   <- term -|- defTerm; return $ flip (foldr ($)) chs . f
  where
    ld_choice = chc <|> def
    chc = do
      token' "choose"; (q, f, vs) <- declared $ art >> notion
      return $ flip (foldr dExi) vs . And (q f)
    def = do
      token' "define"; x <- var; xDecl <- makeDecl x; token "="
      ap <- ld_set <|> lambda
      return $ dExi xDecl . And (Tag Defined $ ap $ pVar x)

    term = fmap ((.) (Tag Evaluation) . flip zEqu) sTerm
    defTerm = do
      ap <- ld_set <|> lambda; h <- hidden; let hv = pVar h
      hDecl <- makeDecl h;
      return $ \fx -> dExi hDecl $
        And (Tag Defined $ ap hv) (Tag Evaluation $ zEqu fx hv)

    ld_set = do (_, t, _) <- set; return $ flip substHole t


lambda :: FTL (Formula -> Formula)
lambda = do
  (t, df_head, dom) <- ld_head; vs <- freeVars t; df <- addDecl vs lambdaBody
  return $ \f -> zFun f `And` Tag Domain (dom f) `And` (df_head f $ df $ zApp f t)
  where
    ld_head = finish $ token "\\" >> lambdaIn

pair :: Parser st Formula
pair = sVar </> pr
  where
    pr = do [l,r] <- smPatt pair pairPattern; return $ zPair l r
    pairPattern = [Sm "(", Vr, Sm ",", Vr, Sm ")"]

lambdaIn :: Parser
              FState (Formula, Formula -> Formula -> Formula, Formula -> Formula)
lambdaIn = do
  t <- pair; vs <- freeVarPositions t; vsDecl <- mapM makeDecl vs
  token' "in"; dom <- ld_dom;
  let df_head f = foldr ((.) . dAll) (Imp (t `zElem` zDom f)) vsDecl
  return (t, df_head, \f -> dom f t vsDecl)
  where
    ld_dom = trm <|> setTrm
    trm = do
      t <- sTerm; return $ \f _ _ -> zDom f `zEqu` t
    setTrm = do
      (ap, _) <- symbSetNotation
      return $ \f t -> foldr dAll (Iff (t `zElem` zDom f) (ap t))

---- chain tools

multExi :: Foldable t1 =>
           [(t2 -> Formula, t2, t1 Decl.Decl)] -> Formula
multExi ((q, f, vs):ns) = foldr mbdExi (q f `blAnd` multExi ns) vs
multExi [] = Top

conjChain :: Parser st Formula -> Parser st Formula
conjChain = fmap (foldl1 And) . flip sepBy (token' "and")

quChain :: FTL (Formula -> Formula)
quChain = fmap (foldl fld id) $ token' "for" >> quNotion `sepByLL1` comma
-- we can use LL1 here, since there must always follow a parser belonging to the
-- same non-terminal
  where
    fld x (y, _) = x . y


-- Digger

dig :: Monad m => Formula -> [Formula] -> m Formula
dig f [_] | occursS f = fail "too few subjects for an m-predicate"
dig f ts = return (dive f)
  where
    dive :: Formula -> Formula
    dive (Tag Dig f) = down digS f
    dive (Tag DigMultiSubject f) = down (digM $ zip ts $ tail ts) f
    dive (Tag DigMultiPairwise f) = down (digM $ pairMP ts) f
    dive f | isTrm f = f
    dive f = mapF dive f

    down :: (Formula -> [Formula]) -> Formula -> Formula
    down fn (And f g) = And (down fn f) (down fn g)
    down fn f = foldl1 And (fn f)

    digS :: Formula -> [Formula]
    digS f
      | occursH f = map ( `substHole` f) ts
      | otherwise = [f]

    digM :: [(Formula, Formula)] -> Formula -> [Formula]
    digM ps f
      | not (occursS f) = digS f
      | not (occursH f) = map ( `substSlot` f) $ tail ts
      | otherwise = map (\ (x,y) -> substSlot y $ substHole x f) ps

-- Example:
-- pairMP [1,2,3,4]
-- [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
pairMP :: [a] -> [(a, a)]
pairMP (t:ts) = [ (t, s) | s <- ts ] ++ pairMP ts
pairMP _ = []
