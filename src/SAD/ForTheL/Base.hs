{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

FoTheL state and state management, parsing of primitives, operations on
variables and macro expressions.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Base where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Class (gets, modify)
import Data.Char (isAlpha, isAlphaNum)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Set (Set)
import qualified Data.Set as Set

import SAD.Data.Formula

import SAD.Parser.Base
import SAD.Parser.Combinators
import SAD.Parser.Primitives

import SAD.Core.SourcePos (noSourcePos)

import SAD.Data.Text.Decl (Decl(Decl))
import SAD.Data.Text.Decl

import SAD.Core.Message (PIDE)
import qualified SAD.Core.Message as Message
import SAD.Core.Pretty (pretty)

type FTL = Parser FState

-- Unary terms and notions.
type UTerm   = (Formula -> Formula, Formula)
type UNotion = (Formula -> Formula, Formula, PosVar)

-- Multi-terms and -notions.
type MTerm   = (Formula -> Formula, [Formula])
type MNotion = (Formula -> Formula, Formula, Set PosVar)

type Prim    = ([Pattern], [Formula] -> Formula)


data FState = FState {
  adjectiveExpr, verbExpr, notionExpr, symbNotionExpr :: [Prim],
  cfnExpr, rfnExpr, lfnExpr, ifnExpr :: [Prim],
  cprExpr, rprExpr, lprExpr, iprExpr :: [Prim],

  tvrExpr :: [TVar], strSyms :: [[Text]], varDecl :: Set VarName,
  idCount :: Int, hiddenCount :: Int, serialCounter :: Int,
  reports :: [Message.Report], pide :: Maybe PIDE }


initFS :: Maybe PIDE -> FState
initFS = FState
  primAdjs [] primNotions primSymbNotions
  cf rf [] []
  [] [] [] primInfixPredicates
  [] [] mempty
  0 0 0
  []
  where
    primAdjs = [
      ([Word ["equal"], Word ["to"], Vr], mkTrm EqualityId TermEquality),
      ([Word ["nonequal"], Word ["to"], Vr], Not . mkTrm EqualityId TermEquality) ]
    primNotions = [
      ([Word ["function","functions"], Nm], mkFun . head),
      ([Word ["set","sets"], Nm], mkSet . head),
      ([Word ["element", "elements"], Nm, Word ["of"], Vr], \(x:m:_) -> mkElem x m),
      ([Word ["object", "objects"], Nm], mkObj . head)]
    primSymbNotions = [ ([Symbol "=", Vr], mkTrm EqualityId TermEquality) ]
    primInfixPredicates = [
      ([Symbol "="], mkTrm EqualityId TermEquality),
      ([Symbol "!", Symbol "="], Not . mkTrm EqualityId TermEquality),
      ([Symbol "-", Symbol "<", Symbol "-"], mkTrm LessId TermLess),
      ([Symbol "-~-"], \(m:n:_) -> mkAll VarEmpty $
        Iff (mkElem (mkVar VarEmpty) m) (mkElem (mkVar VarEmpty) n)) ]
    cf = [
      ([Symbol "Dom", Symbol "(",Vr,Symbol ")"], mkDom . head),
      ([Symbol "(", Vr, Symbol ",", Vr, Symbol ")"], \(x:y:_) -> mkPair x y) ]
    rf = [ ([Symbol "[", Vr, Symbol "]"], \(f:x:_) -> mkApp f x)]


getExpr :: (FState -> [a]) -> (a -> FTL b) -> FTL b
getExpr e p = gets e >>=  foldr ((-|-) . try . p ) mzero


getDecl :: FTL (Set VarName)
getDecl = gets varDecl

addDecl :: Set VarName -> FTL a -> FTL a
addDecl vs p = do
  dcl <- gets varDecl; modify adv;
  after p $ modify $ sbv dcl
  where
    adv s = s { varDecl = vs <> varDecl s }
    sbv vs s = s { varDecl = vs }

getPretyped :: FTL [TVar]
getPretyped = gets tvrExpr

makeDecl :: PosVar -> FTL Decl
makeDecl (PosVar nm pos) = do
  serial <- gets serialCounter
  modify (\st -> st {serialCounter = serial + 1})
  return $ Decl nm pos (serial + 1)

makeDecls :: Set PosVar -> FTL (Set Decl)
makeDecls = Set.foldr (\v f -> makeDecl v >>= \d -> Set.insert d <$> f) (pure mempty)

declared :: MNotion -> FTL (Formula -> Formula, Formula, Set Decl)
declared (q, f, v) = do nv <- makeDecls v; return (q, f, nv)

-- Predicates: verbs and adjectiveectives

primVer, primAdj, primUnAdj :: FTL UTerm -> FTL UTerm

primVer = getExpr verbExpr . primPrd
primAdj = getExpr adjectiveExpr . primPrd
primUnAdj = getExpr (filter (unary . fst) . adjectiveExpr) . primPrd
  where
    unary pt = Vr `notElem` pt

primPrd :: FTL (b1 -> b1, Formula)
           -> ([Pattern], [Formula] -> b2) -> FTL (b1 -> b1, b2)
primPrd p (pt, fm) = do
  (q, ts) <- wdPattern p pt
  return (q, fm $ (mkVar (VarHole "")):ts)


-- Multi-subject predicates: [a,b are] equal

primMultiVer, primMultiAdj, primMultiUnAdj :: FTL UTerm -> FTL UTerm

primMultiVer = getExpr verbExpr . primMultiPredicate
primMultiAdj = getExpr adjectiveExpr . primMultiPredicate
primMultiUnAdj = getExpr (filter (unary . fst) . adjectiveExpr) . primMultiPredicate
  where
    unary (Vr : pt) = Vr `notElem` pt
    unary (_  : pt) = unary pt
    unary [] = True

primMultiPredicate :: FTL (b1 -> b1, Formula)
               -> ([Pattern], [Formula] -> b2) -> FTL (b1 -> b1, b2)
primMultiPredicate p (pt, fm) = do
  (q, ts) <- multiPattern p pt
  return (q, fm $ (mkVar (VarHole "")):(mkVar VarSlot):ts)


-- Notions and functions


primNotion :: FTL UTerm -> FTL MNotion
primNotion p  = getExpr notionExpr notion
  where
    notion (pt, fm) = do
      (q, vs, ts) <- notionPattern p pt
      return (q, fm $ (mkVar (VarHole "")):ts, vs)

primOfNotion :: FTL UTerm -> FTL MNotion
primOfNotion p = getExpr notionExpr notion
  where
    notion (pt, fm) = do
      (q, vs, ts) <- ofPattern p pt
      let fn v = fm $ (pVar v):(mkVar (VarHole "")):ts
      return (q, foldr1 And $ map fn $ Set.toList vs, vs)

primCommonNotion :: FTL UTerm -> FTL MTerm -> FTL MNotion
primCommonNotion p s = getExpr notionExpr notion
  where
    notion (pt, fm) = do
      (q, vs, as, ts) <- commonPattern p s pt
      let fn v = fm $ (mkVar (VarHole "")):v:ts
      return (q, foldr1 And $ map fn as, vs)

primFun :: FTL UTerm -> FTL UTerm
primFun  = (>>= fun) . primNotion
  where
    fun (q, Trm {trmName = TermEquality, trmArgs = [_, t]}, _)
      | not (occursH t) = return (q, t)
    fun _ = mzero


-- Symbolic primitives

primCpr :: FTL Formula -> FTL Formula
primCpr = getExpr cprExpr . primCsm
primRpr :: FTL Formula -> FTL (Formula -> Formula)
primRpr = getExpr rprExpr . primRsm
primLpr :: FTL Formula -> FTL (Formula -> Formula)
primLpr = getExpr lprExpr . primLsm
primIpr :: FTL Formula
           -> FTL (Formula -> Formula -> Formula)
primIpr = getExpr iprExpr . primIsm

primCfn :: FTL Formula -> FTL Formula
primCfn = getExpr cfnExpr . primCsm
primRfn :: FTL Formula -> FTL (Formula -> Formula)
primRfn = getExpr rfnExpr . primRsm
primLfn :: FTL Formula -> FTL (Formula -> Formula)
primLfn = getExpr lfnExpr . primLsm
primIfn :: FTL Formula
           -> FTL (Formula -> Formula -> Formula)
primIfn = getExpr ifnExpr . primIsm

primCsm :: FTL a -> ([Pattern], [a] -> b) -> FTL b
primCsm p (pt, fm) = symbolPattern p pt >>= \l -> return $ fm l
primRsm :: FTL a -> ([Pattern], [a] -> t) -> FTL (a -> t)
primRsm p (pt, fm) = symbolPattern p pt >>= \l -> return $ \t -> fm $ t:l
primLsm :: FTL a -> ([Pattern], [a] -> t) -> FTL (a -> t)
primLsm p (pt, fm) = symbolPattern p pt >>= \l -> return $ \s -> fm $ l++[s]
primIsm :: FTL a
           -> ([Pattern], [a] -> t) -> FTL (a -> a -> t)
primIsm p (pt, fm) = symbolPattern p pt >>= \l -> return $ \t s -> fm $ t:l++[s]


primSnt :: FTL Formula -> FTL MNotion
primSnt p  = noError $ varList >>= getExpr symbNotionExpr . snt
  where
    snt vs (pt, fm) = symbolPattern p pt >>= \l -> return (id, fm $ (mkVar (VarHole "")):l, vs)




data Pattern = Word [Text] | Symbol Text | Vr | Nm deriving (Eq, Show)


-- adding error reporting to pattern parsing
patternTokenOf' :: [Text] -> FTL ()
patternTokenOf' l = label ("a word of " <> Text.pack (show l)) $ tokenOf' l

patternSymbolTokenOf :: Text -> FTL ()
patternSymbolTokenOf l = label ("the symbol " <> Text.pack (show l)) $ token l

-- most basic pattern parser: simply follow the pattern and parse terms with p
-- at variable places
wdPattern :: FTL (b -> b, a) -> [Pattern] -> FTL (b-> b, [a])
wdPattern p (Word l : ls) = patternTokenOf' l >> wdPattern p ls
wdPattern p (Vr : ls) = do
  (r, t) <- p
  (q, ts) <- wdPattern p ls
  return (r . q, t:ts)
wdPattern _ [] = return (id, [])
wdPattern _ _ = mzero

-- parses a symbolic pattern
symbolPattern :: FTL a -> [Pattern] -> FTL [a]
symbolPattern p (Vr : ls) = liftM2 (:) p $ symbolPattern p ls
symbolPattern p (Symbol s : ls) = patternSymbolTokenOf s >> symbolPattern p ls
symbolPattern _ [] = return []
symbolPattern _ _ = mzero

-- parses a multi-subject pattern: follow the pattern, but ignore the token'
-- right before the first variable. Then check that all "and" tokens have been
-- consumed. Example pattern: [Word ["commute","commutes"], Word ["with"], Vr]. Then
-- we can parse "a commutes with c and d" as well as "a and b commute".
multiPattern :: FTL (b -> b, a) -> [Pattern] -> FTL (b -> b, [a])
multiPattern p (Word l :_: Vr : ls) = patternTokenOf' l >> naPattern p ls
multiPattern p (Word l : ls) = patternTokenOf' l >> multiPattern p ls
multiPattern _ _ = mzero


-- parses a notion: follow the pattern to the name place, record names,
-- then keep following the pattern
notionPattern :: FTL (b -> b, a)
          -> [Pattern] -> FTL (b -> b, Set PosVar, [a])
notionPattern p (Word l : ls) = patternTokenOf' l >> notionPattern p ls
notionPattern p (Nm : ls) = do
  vs <- nameList
  (q, ts) <- wdPattern p ls
  return (q, vs, ts)
notionPattern _ _ = mzero

-- parse an "of"-notion: follow the pattern to the notion name, then check that
-- "of" follows the name followed by a variable that is not followed by "and"
ofPattern :: FTL (b -> b, a)
          -> [Pattern] -> FTL (b -> b, Set PosVar, [a])
ofPattern p (Word l : ls) = patternTokenOf' l >> ofPattern p ls
ofPattern p (Nm : Word l : Vr : ls) = do
  guard $ elem "of" l; vs <- nameList
  (q, ts) <- naPattern p ls
  return (q, vs, ts)
ofPattern _ _ = mzero

-- | parse a "common"-notion: basically like the above. We use the special parser
-- s for the first variable place after the "of" since we expect multiple terms
-- here. Example: A common *divisor of m and n*.
commonPattern :: FTL (b -> b, a1)
          -> FTL (b -> c, [a2])
          -> [Pattern]
          -> FTL (b -> c, Set PosVar, [a2], [a1])
commonPattern p s (Word l:ls) = patternTokenOf' l >> commonPattern p s ls
commonPattern p s (Nm : Word l : Vr : ls) = do
  guard $ elem "of" l; vs <- nameList; patternTokenOf' l
  (r, as) <- s
  when (null $ tail as) $ fail "several objects expected for `common'"
  (q, ts) <- naPattern p ls
  return (r . q, vs, as, ts)
commonPattern _ _ _ = mzero

-- an auxiliary pattern parser that checks that we are not dealing with an "and"
-- token' and then continues to follow the pattern
naPattern :: FTL (b -> b, a)
          -> [Pattern] -> FTL (b -> b, [a])
naPattern p (Word l : ls) = guard (notElem "and" l) >> patternTokenOf' l >> wdPattern p ls
naPattern p ls = wdPattern p ls



-- Variables

nameList :: FTL (Set PosVar)
nameList = varList -|- fmap Set.singleton hidden

varList :: FTL (Set PosVar)
varList = var `sepBy` token' "," >>= nodups

nodups :: IsVar a => [a] -> FTL (Set a)
nodups vs = do
  unless ((null :: [b] -> Bool) $ duplicateNames vs) $
    fail $ "duplicate names: " ++ (show $ map (Text.unpack . pretty) vs)
  pure $ Set.fromList vs

hidden :: FTL PosVar
hidden = do
  n <- gets hiddenCount
  modify $ \st -> st {hiddenCount = succ n}
  return (PosVar (VarHidden n) noSourcePos)

-- | Parse the next token as a variable (a sequence of alpha-num chars beginning with an alpha)
-- and return ('x' + the sequence) with the current position.
var :: FTL PosVar
var = do
  pos <- getPos
  v <- satisfy (\s -> Text.all isAlphaNum s && isAlpha (Text.head s))
  return (PosVar (VarConstant v) pos)

--- pretyped Variables

type TVar = (Set VarName, Formula)

primTypedVar :: FTL MNotion
primTypedVar = getExpr tvrExpr tvr
  where
    tvr (vr, nt) = do
      vs <- varList
      guard $ Set.foldr (\v b -> b && v `Set.member` vr) True $ Set.map posVarName vs
      return (id, nt, vs)

-- free

freeVars :: IsVar a => Formula -> FTL (FV a)
freeVars f = excludeSet (free f) <$> getDecl

--- decl

{- produce the variables declared by a formula together with their positions. As
parameter we pass the already known variables-}
decl :: IsVar a => Formula -> FV a
decl = dive
  where
    dive (All _ f) = dive f
    dive (Exi _ f) = dive f
    dive (Tag _ f) = dive f
    dive (Imp f g) = excludeVars (allFree f) (dive g)
    dive (And f g) = dive f <> excludeVars (allFree f) (dive g)
    dive t@Trm {trmArgs = v@Var{varName = u@(VarConstant _)}:ts}
      | isNotion t && all (\t -> not (v `occursIn` t)) ts = unitFV u (varPosition v)
    dive Trm{trmName = TermEquality, trmArgs = [v@Var{varName = u@(VarConstant _)}, t]}
      | isTrm t && not (v `occursIn` t) = unitFV u (varPosition v)
    dive _ = mempty

{- produce variable names declared by a formula -}
declNames :: Set VarName -> Formula -> Set VarName
declNames vs f = fvToVarSet $ excludeSet (decl f) vs

{- produce the bindings in a formula in a Decl data type and take care of
the serial counter. -}
bindings :: Set VarName -> Formula -> FTL (Set Decl)
bindings vs f = makeDecls $ fvToVarSet $ excludeSet (decl f) vs


freeOrOverlapping :: Set VarName -> Formula -> Maybe Text
freeOrOverlapping vs f
    | (mkVar VarSlot) `occursIn` f = Just $ "too few subjects for an m-predicate " <> info
    | not (Text.null sbs) = Just $ "free undeclared variables: "   <> sbs <> info
    | not (Text.null ovl) = Just $ "overlapped variables: "        <> ovl <> info
    | otherwise      = Nothing
  where
    sbs = Text.unwords $ map (showVar) $ Set.toList $ fvToVarSet $ excludeSet (free f) vs
    ovl = Text.unwords $ map (showVar) $ Set.toList $ over vs f
    info = "\n in translation: " <> (Text.pack $ showFormula f)

    over :: Set VarName -> Formula -> Set VarName
    over vs (All v f) = boundVars vs (declName v) f
    over vs (Exi v f) = boundVars vs (declName v) f
    over vs f = foldF (over vs) f

    boundVars :: Set VarName -> VarName -> Formula -> Set VarName
    boundVars vs v f
      | v `Set.member` vs = Set.singleton v
      | v == VarEmpty = over vs f
      | otherwise = over (Set.insert v vs) f


--- macro expressions


comma :: FTL ()
comma = tokenOf' [",", "and"]
is :: FTL ()
is = tokenOf' ["is", "be", "are"]
art :: FTL ()
art = opt () $ tokenOf' ["a","an","the"]
an :: FTL ()
an = tokenOf' ["a", "an"]
the :: FTL ()
the = token' "the"
iff :: FTL ()
iff = token' "iff" <|> mapM_ token' ["if", "and", "only", "if"]
that :: FTL ()
that = token' "that"
standFor :: FTL ()
standFor = token' "denote" <|> (token' "stand" >> token' "for")
arrow :: FTL ()
arrow = symbol "->"
there :: FTL ()
there = token' "there" >> tokenOf' ["is","exist","exists"]
does :: FTL ()
does = opt () $ tokenOf' ["does", "do"]
has :: FTL ()
has = tokenOf' ["has" , "have"]
with :: FTL ()
with = tokenOf' ["with", "of", "having"]
such :: FTL ()
such = tokenOf' ["such", "so"]



texBegin, texEnd :: Text -> FTL Text
texBegin env = do
  token "\\begin"
  symbol "{"
  token env
  symbol "}"
  return env

texEnd env = do
  token "\\end"
  symbol "{"
  token env
  symbol "}"
  return env


--just for now:

showVar :: VarName -> Text
showVar (VarConstant nm) = nm
showVar nm =  pretty nm
