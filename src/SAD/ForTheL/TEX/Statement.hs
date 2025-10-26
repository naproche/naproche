-- |
-- Module      : SAD.ForTheL.TEX.Statement
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2025 Marcel Schütz
-- License     : GPL-3
--
-- Statements (TeX).


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.TEX.Statement (
  statement,
  anotion,
  choice,
  classNotion,
  mapNotion
) where


import Data.Set (Set)
import Data.Function ((&))
import Control.Applicative ((<**>), Alternative(..))
import Control.Monad (guard)
import Data.Set qualified as Set

import SAD.Data.Formula
import SAD.Data.Text.Decl
import SAD.ForTheL.Base
import SAD.ForTheL.Statement
import SAD.ForTheL.Reports (markupToken, markupTokenOf, markupTokenSeqOf)
import SAD.Parser.Combinators
import SAD.Parser.Primitives (token, token', symbol, tokenOf', tokenSeq', tokenSeqOf')
import SAD.ForTheL.Reports qualified as Reports


statement :: FTL Formula
statement = headed <|> chained

headed :: FTL Formula
headed = quantifiedStatement <|> ifThenStatement <|> wrongStatement
  where
    quantifiedStatement = quantifierChain <*> statement
    ifThenStatement = liftA2 Imp
      (markupToken Reports.ifThen "if" >> statement)
      (markupToken Reports.ifThen "then" >> statement)
    wrongStatement = try $
      tokenSeq' ["it", "is", "wrong", "that"] >> fmap Not statement


chained :: FTL Formula
chained = label "chained statement" $ (andOr <|> neitherNor) >>= chainEnd
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
chainEnd f = optLL1 f $ and_st <|> or_st <|> iff_st <|> imp_st <|> where_st
  where
    and_st = fmap (And f) $ markupToken Reports.conjunctiveAnd "and" >> headed
    or_st = fmap (Or f) $ markupToken Reports.or "or" >> headed
    iff_st = fmap (Iff f) $ markupTokenSeqOf Reports.ifAndOnlyIf iffPhrases >> statement
    imp_st = fmap (Imp f) $ markupToken Reports.ifThen "implies" >> opt () (token' "that") >> statement
    where_st = do
      markupTokenOf Reports.whenWhere ["when", "where"]; y <- statement
      return $ foldr mkAll (Imp y f) (declNames mempty y)


atomic :: FTL Formula
atomic = label "atomic statement"
  thereIs <|> (simple </> (weHave >> symbolicStatement <|> thesis))
  where
    weHave = optLL1 () $ tokenSeqOf' [
        ["we", "have"],
        ["it", "holds", "that"]
      ]


thesis :: FTL Formula
thesis = (thes </> contrary) <|> contradiction
  where
    thes = tokenSeq' ["the", "thesis"] >> return mkThesis
    contrary = tokenSeq' ["the", "contrary"] >> return (Not mkThesis)
    contradiction = opt() (token' "a") >> token' "contradiction" >> return Bot


thereIs :: FTL Formula
thereIs = label "there-is statement" $ token' "there" >> tokenOf' ["is", "are", "exist", "exists"] >> (noNotion -|- notions)
  where
    noNotion = label "no-notion" $ do
      token' "no"; (q, f, vs) <- declared =<< notion;
      return $ Not $ foldr mbdExi (q f) vs
    notions = fmap multExi $ opt () (tokenOf' ["a", "an"]) >> (declared =<< notion) `sepBy` tokenOf' [",", "and"]


simple :: FTL Formula
simple = label "simple statement" $ do
  (q, ts) <- terms
  p  <- conjChain doesPredicate
  q' <- lateQuantifiers
  q . q' <$> dig p ts

-- |
-- A symbolic statement is either a symbolic formula or the assertion that two class
-- terms are equal, followed by optional later quantifiers. If no quantifiers are present
-- the statement is returned as-is, otherwise the quantifiers are applied to the statement.
--
symbolicStatement :: FTL Formula
symbolicStatement = label "a symbolic statement" $
  (symbolicFormula -|- classEquality -|- alignEnvironment) <**> lateQuantifiers

-- |
-- Parse late quantifiers yielding a quantifying function.
-- Defaults to @id@ when there are no quantifiers.
--
lateQuantifiers :: FTL (Formula -> Formula)
lateQuantifiers = optLL1 id quantifierChain


--- predicates


doesPredicate :: FTL Formula
doesPredicate = label "does predicate" $
  (opt () (tokenOf' ["does", "do"]) >> (doP -|- multiDoP)) <|> hasP <|> isChain
  where
    doP = predicate primVer
    multiDoP = multiPredicate primMultiVer
    hasP = tokenOf' ["has" , "have"] >> hasPredicate
    isChain = tokenOf' ["is", "are", "be"] >> conjChain (isAPredicate -|- isPredicate)


isPredicate :: FTL Formula
isPredicate = label "is predicate" $
  pAdj -|- pMultiAdj -|- (tokenOf' ["with", "of", "having"] >> hasPredicate)
  where
    pAdj = predicate primAdj
    pMultiAdj = multiPredicate primMultiAdj


isAPredicate :: FTL Formula
isAPredicate = label "isA predicate" $ notNotion <|> notion
  -- Unlike the language description, we distinguish positive and negative
  -- rather than notions and fixed terms.
  where
    notion = fmap (uncurry ($)) anotion
    notNotion = do
      token' "not"; (q, f) <- anotion
      let unfinished = dig f [(mkVar (VarHole ""))]
      optLLx (q $ Not f) $ fmap (q. Tag Dig . Not) unfinished

hasPredicate :: FTL Formula
hasPredicate = label "has predicate" $ noPossessive <|> possessive
  where
    possessive = opt () (tokenOf' ["a", "an"]) >> common <|> nonbinary
    nonbinary = fmap (Tag Dig . multExi) $ (declared =<< possess) `sepBy` (tokenOf' [",", "and"] >> opt () (tokenOf' ["a", "an"]))
    common = token' "common" >>
      fmap multExi (fmap digadd (declared =<< possess) `sepBy` tokenOf' [",", "and"])

    noPossessive = nUnary -|- nCommon
    nUnary = do
      token' "no"; (q, f, v) <- declared =<< possess;
      return $ q . Tag Dig . Not $ foldr mbdExi f v
    nCommon = do
      token' "no"; token' "common"; (q, f, v) <- declared =<< possess
      return $ q . Not $ foldr mbdExi (Tag Dig f) v
      -- take a closer look at this later.. why is (Tag Dig) *inside* important?


--- predicate parsing

predicate :: (FTL UTerm -> FTL UTerm) -> FTL Formula
predicate p = (token' "not" >> negative) <|> positive
  where
    positive = do (q, f) <- p term; return $ q . Tag Dig $ f
    negative = do (q, f) <- p term; return $ q . Tag Dig . Not $ f

multiPredicate :: (FTL UTerm -> FTL UTerm) -> FTL Formula
multiPredicate p = (token' "not" >> mNegative) <|> mPositive
  where
    mPositive = (token' "pairwise" >> pPositive) <|> sPositive
    -- we distinguish between *separate* and *pairwise*
    sPositive = do (q, f) <- p term; return $ q . Tag DigMultiSubject $ f
    pPositive = do (q, f) <- p term; return $ q . Tag DigMultiPairwise $ f

    mNegative = (token' "pairwise" >> pNegative) <|> sNegative
    sNegative = do (q, f) <- p term; return $ q . Tag DigMultiSubject . Not $ f
    pNegative = do (q, f) <- p term; return $ q . Tag DigMultiPairwise . Not $ f




--- Notions

baseNotion :: FTL (Formula -> Formula, Formula, Set PosVar)
baseNotion = fmap digadd $ cm <|> symEqnt <|> (collection </> primNotion term)
  where
    cm = token' "common" >> primCommonNotion term terms
    symEqnt = do
      t <- lexicalCheck isTrm sTerm
      v <- hidden;
      pure (id, mkEquality (mkVar (VarHole "")) t, Set.singleton v)

symNotion :: FTL (Formula -> Formula, Formula, Set PosVar)
symNotion = do
  x <- optParenthesised (primSnt sTerm) </> primTypedVar
  digNotion (digadd x)


gnotion :: FTL (Formula -> Formula, Formula, Set PosVar)
  -> FTL Formula -> FTL (Formula -> Formula, Formula, Set PosVar)
gnotion nt ra = do
  ls <- fmap reverse la; (q, f, vs) <- nt;
  rc <- opt [] $ fmap (:[]) (conjChain isPredicate)
  rs <- opt [] $ fmap (:[]) $ ra <|> thatClause
  -- we can use <|> here because every ra in use begins with "such"
  return (q, foldr1 And $ f : ls ++ rc ++ rs, vs)
  where
    la = opt [] $ liftA2 (:) lc la
    lc = predicate primUnAdj </> multiPredicate primMultiUnAdj
    thatClause = token' "that" >> conjChain doesPredicate <?> "that clause"


anotion :: FTL (Formula -> Formula, Formula)
anotion = label "notion (at most one name)" $
  opt () (tokenOf' ["a", "an", "the"]) >> gnotion baseNotion rat >>= single >>= hole
  where
    hole (q, f, v) = return (q, subst (mkVar (VarHole "")) (posVarName v) f)
    rat = fmap (Tag Dig) suchThatAttr

notion :: FTL (Formula -> Formula, Formula, Set PosVar)
notion = label "notion" $ gnotion (baseNotion </> symNotion) suchThatAttr >>= digNotion

possess :: FTL (Formula -> Formula, Formula, Set PosVar)
possess = label "possesive notion" $ gnotion (primOfNotion term) suchThatAttr >>= digNotion


suchThatAttr :: FTL Formula
suchThatAttr = label "such-that attribute" $ tokenOf' ["such", "so"] >> token' "that" >> statement


--- terms

terms :: FTL (Formula -> Formula, [Formula])
terms = label "terms" $
  foldl1 alg <$> (subTerm `sepBy` tokenOf' [",", "and"])
  where
    subTerm = quantifiedNotion -|- fmap toMulti definiteTerm
    toMulti (q, t) = (q, [t])
    alg (q, ts) (r, ss) = (q . r, ts ++ ss)

term :: FTL UTerm
term = label "a term" $ (quantifiedNotion >>= toSing) -|- definiteTerm
  where
    toSing (q, [t]) = return (q, t)
    toSing _ = fail "inadmissible multinamed notion"

-- Returns a quantifying function and a list of variables as expression
quantifiedNotion :: FTL (Formula -> Formula, [Formula])
quantifiedNotion = label "quantified notion" $
  optParenthesised (universal <|> existential <|> no)
  where
    universal = do
      tokenOf' ["every", "each", "all", "any"]; (q, f, v) <- notion
      vDecl <- makeDecls v
      return (q . flip (foldr dAll) vDecl . blImp f, pVar <$> Set.toList v)

    existential = do
      token' "some"; (q, f, v) <- notion
      vDecl <- makeDecls v
      return (q . flip (foldr dExi) vDecl . blAnd f, pVar <$> Set.toList v)

    no = do
      token' "no"; (q, f, v) <- notion
      vDecl<- makeDecls v
      return (q . flip (foldr dAll) vDecl . blImp f . Not, pVar <$> Set.toList v)


definiteTerm :: FTL (Formula -> Formula, Formula)
definiteTerm = label "definiteTerm" $  symbolicTerm -|- definiteNoun
  where
    definiteNoun = label "definiteNoun" $ optParenthesised (opt () (token' "the") >> primFun term)



--- symbolic notation


symbolicFormula :: FTL Formula
symbolicFormula  = label "a symbolic formula" $ biimplication
  where
    biimplication = implication >>= binary Iff (symbolicIff >> implication)
    implication   = disjunction >>= binary Imp (symbolicImp >> implication)
    disjunction   = conjunction >>= binary Or  (symbolicOr >> disjunction)
    conjunction   = nonbinary   >>= binary And (symbolicAnd >> conjunction)
    universal     = liftA2 (quantified dAll Imp) (symbolicAll >> (declared =<< symNotion)) nonbinary
    existential   = liftA2 (quantified dExi And) (symbolicExists >> (declared =<< symNotion)) nonbinary
    nonbinary     = truth -|- falsity -|- universal -|- existential -|- negation -|- separated -|- atomic
    truth         = symbolicTruth >> pure Top
    falsity       = symbolicFalsity >> pure Bot
    negation      = Not <$> (symbolicNot >> nonbinary)
    separated     = token' ":" >> symbolicFormula

    quantified quant op (_, f, v) = flip (foldr quant) v . op f

    binary op p f = optLL1 f $ fmap (op f) p

    symbolicIff = token "\\iff"
    symbolicImp = token "\\implies"
    symbolicOr = token "\\vee"
    symbolicAnd = token "\\wedge"
    symbolicAll = token "\\forall"
    symbolicExists = token "\\exists"
    symbolicNot = token "\\neg"
    symbolicTruth = token "\\top"
    symbolicFalsity = token "\\bot"

    atomic = relation -|- parenthesised statement
      where
        relation = sChain </> primCpr sTerm

        sChain = fmap (foldl1 And . concat) sHd

        -- TODO: Rename with slightly more obvious names.
        -- First guess at the meaning of the naming:
        -- s = symbolic
        -- Hd = head
        -- l = left
        -- i = infix
        -- r = right
        --
        -- Combining of the two sides could probably be made
        -- clearer by using list comprehensions.

        sHd = lHd -|- (termChain >>= sTl)
        lHd = do
          pr <- primLpr sTerm
          rs <- termChain
          fmap (map pr rs :) $ opt [] $ sTl rs

        sTl ls = iTl ls -|- rTl ls
        iTl ls = do
          pr <- primIpr sTerm; rs <- termChain
          fmap (liftA2 pr ls rs :) $ opt [] $ sTl rs
        rTl ls = do pr <- primRpr sTerm; return [map pr ls]

        termChain = sTerm `sepBy` token' ","


-- class term equations

classEquality :: FTL Formula
classEquality = label "a class equality" $ twoClassTerms </> oneClassTerm
  where
    twoClassTerms = do
      cnd1 <- fmap stripClass symbClassNotation; token "="
      cnd2 <- fmap stripClass symbClassNotation; h <- hidden
      hDecl <- makeDecl h
      let hv = pVar h
      return $ dAll hDecl $ Imp (mkObject hv) $ Iff (cnd1 hv) (cnd2 hv)
    stripClass = (.) strip . fst

    oneClassTerm = left </> right
    left = do
      cnd <- fmap stripClass symbClassNotation; token "="
      t <- sTerm; h <- hidden; hDecl <- makeDecl h; let hv = pVar h
      return $ And (mkClass t) $ All hDecl $ Iff (cnd hv) (mkElem hv t)
    right = do
      t <- sTerm; token "="; h <- hidden; hDecl <- makeDecl h
      let hv = pVar h
      cnd <- fmap stripClass symbClassNotation
      return $ And (mkClass t) $ dAll hDecl $ Iff (mkElem hv t) (cnd hv)


-- Align Environments

alignEnvironment :: FTL Formula
alignEnvironment = label "an \"align*\" environment" $ do
  texBegin $ token "align" *> symbol "*"
  headTerm <- sTerm
  atomicRelations <- iTl headTerm
  let conjunction = foldl1 And atomicRelations
  texEnd $ token "align" *> symbol "*"
  return conjunction
  where
    iTl :: Formula -> FTL [Formula]
    iTl ls = label "iTl" $ do
      symbol "&"
      pr <- primIpr sTerm
      rs <- sTerm
      fmap (pr ls rs :) $ opt [] $ token "\\\\" >> iTl rs



-- Choice

choice :: FTL Formula
choice = fmap (foldl1 And) $ (opt () (tokenOf' ["a", "an", "the"]) >> takeLongest namedNotion) `sepByLL1` tokenOf' [",", "and"]
  where
    namedNotion = label "named notion" $ do
      (q, f, vs) <- notion; guard (all isExplicitName $ map posVarName $ Set.toList vs); return $ q f
    isExplicitName (VarConstant _) = True; isExplicitName _ = False


-- Map and class syntax

-- -- classes

classNotion :: FTL Formula
classNotion = do
  v <- after var (token "="); (_, f, _) <- collection
  dig (Tag Dig f) [pVar v]

collection :: FTL MNotion
collection = label "class definition" $ symbClass <|> classOf
  where
    classOf = do
      tokenOf' ["class", "classes", "collection", "collections"];
      nm <- var -|- hidden;
      token' "of" >> (optLL1 () (token' "all"));
      (q, f, u) <- notion >>= single; vnm <- hidden;
      vnmDecl <- makeDecl vnm;
      return (id, setFormula mkClass vnmDecl $ (subst (pVar vnm) (posVarName u) $ q f) `blAnd` mkObject (pVar vnm) , Set.singleton nm)
    symbClass = do
      (cnd, (nm, mkColl)) <- symbClassNotation; h <- hidden
      nmDecl <- makeDecl nm
      return (id, setFormula mkColl nmDecl $ cnd $ pVar nm, Set.singleton h)
    setFormula mkColl dcl = let nm = PosVar (declName dcl) (declPosition dcl) in
      And (mkColl (mkVar (VarHole ""))) . dAll dcl . Iff (mkElem (pVar nm) (mkVar (VarHole "")))


symbClassNotation :: FTL (Formula -> Formula, (PosVar, Formula -> Formula))
symbClassNotation = texClass </> cndClass </> finiteSet
  where
    -- E.g. "\{x, f(y), 5\}"
    finiteSet = do
      token' "\\{"
      ts <- sTerm `sepByLL1` token ","
      h <- hidden
      token' "\\}"
      pure (\tr -> mkObject tr `And` (foldr1 Or $ map (mkEquality tr) ts), (h, mkSet))
    -- E.g. "\{x \in X : x \text{ is less than } y\}"
    cndClass = do
      token' "\\{"
      (tag, c, t, mkColl) <- sepFrom
      st <- (token "|" <|> token ":" <|> token "\\mid") >> optInClasstext statement
      vs <- freeVars t
      vsDecl <- makeDecls $ fvToVarSet vs;
      nm <- if isVar t then pure $ PosVar (varName t) (varPosition t) else hidden
      token' "\\}"
      pure (\tr -> tag $ c tr `blAnd` mkObject tr `blAnd` mbEqu vsDecl tr t st, (nm, mkColl))
    -- E.g. "\class{x \in X | x \text{ is less than } y}".
    texClass = texCommandWithArg "class" $ do
      (tag, c, t, mkColl) <- sepFrom
      st <- symbol "|" >> statement <|> optInClasstext statement
      vs <- freeVars t
      vsDecl <- makeDecls $ fvToVarSet vs;
      nm <- if isVar t then pure $ PosVar (varName t) (varPosition t) else hidden
      pure (\tr -> tag $ c tr `blAnd` mkObject tr `blAnd` mbEqu vsDecl tr t st, (nm, mkColl))



    mbEqu :: Set Decl -> Formula -> Formula -> Formula -> Formula
    mbEqu _ tr Var{varName = v} = subst tr v
    mbEqu vs tr t = \st -> foldr mbdExi (st `And` mkEquality tr t) vs

    sepFrom :: FTL (Formula -> Formula, Formula -> Formula, Formula, Formula -> Formula)
    sepFrom = classSep -|- noSep

    classSep = do
      t <- sTerm
      texCommand "in"
      sep t
    noSep  = do
      t <- sTerm
      return (Tag Replacement, const Top, t, mkClass)
    sep t = do
      clssTrm <- (Left <$> sTerm) </> (Right <$> symbClassNotation)
      case clssTrm of
        Left s -> pure (id, flip mkElem s, t, \v -> mkClass v `And` (mkSet s `Imp` mkSet v))
        Right (cls, (_, mkColl)) -> pure (id, cls, t, mkColl)

-- -- maps

mapNotion :: FTL Formula
mapNotion = sVar <**> (wordMap <|> (token "=" >> lambda))
  where
  wordMap = do
    t <- parenthesised $ twoArguments </> oneArgument
    token "="
    vs <- fvToVarSet <$> freeVars t
    def <- addDecl (Set.map posVarName vs) lambdaBody
    (_, _, dom) <- token' "for" >> classIn
    vsDecl <- makeDecls vs
    --let body f = foldr dAll (Imp (t `mkElem` mkDom f) $ def $ mkApp f t) vsDecl
    let body f = foldr (\x g -> dAll x (mkObject (mkVar (declName x)) `Imp` g)) (Imp (t `mkElem` mkDom f) $ def $ mkApp f t) vsDecl
    return $ \f -> mkMap f `And` Tag Domain (dom f) `And` body f

lambdaBody :: FTL (Formula -> Formula)
lambdaBody = label "map definition" $ optParenthesised $ cases <|> quotedChooseInTerm <|> chooseInTerm
  where
    quotedChooseInTerm = do
      symbol "``"
      choice <- chooseInTerm
      symbol "''"
      return choice

cases  :: FTL (Formula -> Formula)
cases = do
  texBegin (token "cases")
  stanza <- sepBy line (token "\\\\")
  texEnd (token "cases")
  return $ \fx -> foldr1 And $ map ((&) fx) stanza
  where
    line :: FTL (Formula -> Formula)
    line = do
      value <- chooseInTerm
      symbol "&"
      optLL1 () (symbol ":")
      condition <- statement
      return (Tag Condition . Imp condition . value)


chooseInTerm :: FTL (Formula -> Formula)
chooseInTerm = do
  chs <- optLL1 [] $ after (ld_choice `sepByLL1` token ",") (token' "in")
  f   <- term -|- defTerm; return $ flip (foldr ($)) chs . f
  where
    ld_choice = chc <|> def
    chc = do
      markupToken Reports.lowlevelHeader "choose"; (q, f, vs) <- opt () (tokenOf' ["a", "an"]) >> notion >>= declared
      return $ flip (foldr dExi) vs . And (q f)
    def = do
      markupToken Reports.lowlevelHeader "define"; x <- var; xDecl <- makeDecl x; token "="
      ap <- ld_class <|> lambda
      return $ dExi xDecl . And (Tag Defined $ ap $ pVar x)

    term = fmap ((.) (Tag Evaluation) . flip mkEquality) sTerm
    defTerm = do
      ap <- ld_class <|> lambda; h <- hidden; let hv = pVar h
      hDecl <- makeDecl h;
      return $ \fx -> dExi hDecl $
        And (Tag Defined $ ap hv) (Tag Evaluation $ mkEquality fx hv)

    ld_class = do (_, t, _) <- collection; return $ (\f -> subst f (VarHole "") t)


lambda :: FTL (Formula -> Formula)
lambda = do
  (t, df_head, dom) <- ld_head
  vs <- fvToVarSet <$> freeVars t
  df <- addDecl vs lambdaBody
  return $ \f -> mkMap f `And` Tag Domain (dom f) `And` (df_head f $ df $ mkApp f t)
  where
    ld_head = finish $ token "\\fun" >> tex_lambdaIn

tex_lambdaIn :: FTL (Formula, Formula -> Formula -> Formula, Formula -> Formula)
tex_lambdaIn = do
  t <- oneArgument </> parenthesised twoArguments
  vs <- fvToVarSet <$> freeVars t
  vsDecl <- makeDecls vs
  texCommand "in"
  dom <- ld_dom
  let df_head f = foldr ((.) . (\x g -> dAll x (mkObject (mkVar (declName x)) `Imp` g))) (Imp (t `mkElem` mkDom f)) vsDecl
  return (t, df_head, \f -> dom f t vsDecl)

ld_dom :: FTL (Formula -> Formula -> Set Decl -> Formula)
ld_dom = trm <|> setTrm

setTrm :: FTL (Formula -> Formula -> Set Decl -> Formula)
setTrm = do
  (ap, _) <- symbClassNotation
  return $ \f t -> foldr dAll (Iff (t `mkElem` mkDom f) (ap t))


classIn :: FTL (Formula, Formula -> Formula -> Formula, Formula -> Formula)
classIn = do
  t <- oneArgument </> parenthesised twoArguments
  vs <- fvToVarSet <$> freeVars t
  vsDecl <- makeDecls vs
  token' "in" <|> texCommand "in"
  dom <- ld_dom
  let df_head f = foldr ((.) . (\x g -> dAll x (mkObject (mkVar (declName x)) `Imp` g))) (Imp (t `mkElem` mkDom f)) vsDecl
  return (t, df_head, \f -> dom f t vsDecl)


---- chain tools

quantifierChain :: FTL (Formula -> Formula)
quantifierChain = fmap (foldl fld id) $ token' "for" >> quantifiedNotion `sepByLL1` tokenOf' [",", "and"]
-- we can use LL1 here, since there must always follow a parser belonging to the
-- same non-terminal
  where
    fld x (y, _) = x . y

optInClasstext :: FTL a -> FTL a
optInClasstext p = texCommandWithArg "classtext" p <|> p
