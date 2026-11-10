{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.ForTheL.Base
-- Description : FoTheL state and state management, parsing of primitives,
--               operations on variables and macro expressions.
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
module SAD.ForTheL.Base where

import Control.Applicative
import Control.Monad
import Control.Monad.State.Class (gets, modify)

import Data.Char (isAlpha, isAlphaNum)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text

import Isabelle.Bytes (Bytes)
import Isabelle.Bytes qualified as Bytes
import Isabelle.Library (implode_space, make_string)
import Isabelle.Position qualified as Position

import Naproche.Program as Program

import SAD.Data.Formula
import SAD.Data.Pattern
import SAD.Data.Text.Decl
import SAD.Export.Pretty
import SAD.Parser.Base
import SAD.Parser.Char (isAsciiLetter)
import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.Parser.Token (showToken)


-- | Parser for ForTheL texts
type FTL = Parser FState

-- | Unary terms.
type UTerm   = (Formula -> Formula, Formula)

-- | Unary notions.
type UNotion = (Formula -> Formula, Formula, PosVar)

-- | Multi-terms.
type MTerm   = (Formula -> Formula, [Formula])


-- | Multi-notions.
type MNotion = (Formula -> Formula, Formula, Set PosVar)

type PrimPredicate = (PredicatePattern, [Formula] -> Formula)
type PrimNotion = (NotionPattern, [Formula] -> Formula)
type PrimSymbol = (SymbolPattern, [Formula] -> Formula)

-- | ForTheL state
data FState = FState {
  adjectiveExpr :: [PrimPredicate],      -- ^ adjective expressions
  verbExpr :: [PrimPredicate],           -- ^ verb expressions
  notionExpr :: [PrimNotion],         -- ^ notion expressions
  symbNotionExpr :: [PrimSymbol],     -- ^ symbolic notion expressions

  cfnExpr :: [PrimSymbol],            -- ^ circumfix funxtion expressions
  rfnExpr :: [PrimSymbol],            -- ^ right funxtion expressions
  lfnExpr :: [PrimSymbol],            -- ^ left funxtion expressions
  ifnExpr :: [PrimSymbol],            -- ^ infix function expressions

  cprExpr :: [PrimSymbol],            -- ^ circumfix predicate expressions
  rprExpr :: [PrimSymbol],            -- ^ right predicate expressions
  lprExpr :: [PrimSymbol],            -- ^ left predicate expressions
  iprExpr :: [PrimSymbol],            -- ^ infix predicate expressions

  tvrExpr :: [TVar],            -- ^ pretyped variables
  strSyms :: [[Text]],          -- ^ synonyms
  varDecl :: Set VariableName,

  idCount :: Int,
  hiddenCount :: Int,
  serialCounter :: Int,

  reports :: [Position.Report],

  program :: Program.Context
}


-- | Initial state of the parsing process. Provides the following predefined
-- expressions:
--
--  * @"equal" "to" ...@ (notion expression)
--  * @"nonequal" "to" ...@ (notion expression)
--  * @"map" | "maps"@ (notion expression)
--  * @"function" | "functions"@ (notion expression)
--  * @"set" | "sets"@ (notion expression)
--  * @"class" | "classes" | "collection" | "collections"@ (notion expression)
--  * @(["mathematical"] ("object" | "objects")) | "element" | "elements"@ (notion expression)
--  * @("element" | "elements") "of" ...@ (notion expression)
--  * @"(" ... "," ... ")"@ (function expression)
--  * @"...(...)@" (function expression)
--
initFState :: Program.Context -> FState
initFState = FState
  primAdjs [] primNotions primSymbNotions
  circFunctions rightFunctions [] []
  [] [] [] primInfixPredicates
  [] [] mempty
  0 0 0
  []
  where
    primAdjs = [
        equalAdj,
        nonequalAdj,
        inductivelyLessAdj
      ]
    primNotions = [
        mapNotion,
        functionNotion,
        setNotion,
        classNotion,
        objectNotion,
        mathObjectNotion,
        elementOfNotion
      ]
    primSymbNotions = []
    primInfixPredicates = []
    circFunctions = [pairFunction]
    rightFunctions = [applicationFunction]

    -- "equal to x"
    equalAdj = ([PredWord ["equal"], PredWord ["to"], PredVar], mkTrm EqualityId TermEquality)
    -- "nonequal to x"
    nonequalAdj = ([PredWord ["nonequal"], PredWord ["to"], PredVar], Not . mkTrm EqualityId TermEquality)
    -- "inductively less than x"
    inductivelyLessAdj = ([PredWord ["inductively"], PredWord ["less"], PredWord ["than"], PredVar], mkTrm LessId TermLess)
    -- "a map f"
    mapNotion = ([NotionWord ["map", "maps"], NotionName], mkMap . head)
    -- "a function f"
    functionNotion = ([NotionWord ["function", "functions"], NotionName], mkFunction . head)
    -- "a set X"
    setNotion = ([NotionWord ["set", "sets"], NotionName], mkSet . head)
    -- "a class X", "a collection X"
    classNotion = ([NotionWord ["class", "classes", "collection", "collections"], NotionName], mkClass . head)
    -- "an object X", "an element X"
    objectNotion = ([NotionWord ["object", "objects", "element", "elements"], NotionName], mkObject . head)
    -- "a mathematical object"
    mathObjectNotion = ([NotionWord ["mathematical"], NotionWord ["object", "objects"], NotionName], mkObject . head)
    -- "an element x of X"
    elementOfNotion = ([NotionWord ["element", "elements"], NotionName, NotionWord ["of"], NotionVar], \(x:m:_) -> mkElem x m)
    -- "(x,y)"
    pairFunction = ([SymbSymbol "(", SymbVar, SymbSymbol ",", SymbVar, SymbSymbol ")"], \(x:y:_) -> mkPair x y)
    -- "f(x)"
    applicationFunction = ([SymbSymbol "(", SymbVar, SymbSymbol ")"], \(f:x:_) -> mkApp f x)


getExpr :: (FState -> [a]) -> (a -> FTL b) -> FTL b
getExpr e p = gets e >>=  foldr ((-|-) . try . p ) mzero


getDecl :: FTL (Set VariableName)
getDecl = gets varDecl

-- | @addDecl vs p@ temporarily modifies the variable declarations to include
-- @vs@ while running the parser @p@.
addDecl :: Set VariableName -> FTL a -> FTL a
addDecl vs p = do
  dcl <- gets varDecl
  modify adv
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


-- * Predicates: verbs and adjectives

primVer, primAdj, primUnAdj :: FTL UTerm -> FTL UTerm

primVer = getExpr verbExpr . primPrd
primAdj = getExpr adjectiveExpr . primPrd
primUnAdj = getExpr (filter (unary . fst) . adjectiveExpr) . primPrd
  where
    unary pt = PredVar `notElem` pt

primPrd :: FTL (b1 -> b1, Formula)
           -> (PredicatePattern, [Formula] -> b2) -> FTL (b1 -> b1, b2)
primPrd p (pt, fm) = do
  (q, ts) <- predWdPattern p pt
  return (q, fm $ mkVar (VarHole ""):ts)


-- * Multi-subject predicates: [a,b are] equal

primMultiVer, primMultiAdj, primMultiUnAdj :: FTL UTerm -> FTL UTerm

primMultiVer = getExpr verbExpr . primMultiPredicate
primMultiAdj = getExpr adjectiveExpr . primMultiPredicate
primMultiUnAdj = getExpr (filter (unary . fst) . adjectiveExpr) . primMultiPredicate
  where
    unary (PredVar : pt) = PredVar `notElem` pt
    unary (_  : pt) = unary pt
    unary [] = True

primMultiPredicate :: FTL (b1 -> b1, Formula)
               -> (PredicatePattern, [Formula] -> b2) -> FTL (b1 -> b1, b2)
primMultiPredicate p (pt, fm) = do
  (q, ts) <- multiPattern p pt
  return (q, fm $ mkVar (VarHole "") : mkVar VarSlot : ts)


-- * Notions and functions

primNotion :: FTL UTerm -> FTL MNotion
primNotion p = getExpr notionExpr notion
  where
    notion (pt, fm) = do
      (q, vs, ts) <- notionPattern p pt
      return (q, fm $ mkVar (VarHole "") : ts, vs)

primOfNotion :: FTL UTerm -> FTL MNotion
primOfNotion p = getExpr notionExpr notion
  where
    notion (pt, fm) = do
      (q, vs, ts) <- ofPattern p pt
      let fn v = fm $ pVar v : mkVar (VarHole "") : ts
      return (q, foldr1 And $ map fn $ Set.toList vs, vs)

primCommonNotion :: FTL UTerm -> FTL MTerm -> FTL MNotion
primCommonNotion p s = getExpr notionExpr notion
  where
    notion (pt, fm) = do
      (q, vs, as, ts) <- commonPattern p s pt
      let fn v = fm $ mkVar (VarHole "") : v : ts
      return (q, foldr1 And $ map fn as, vs)

primFun :: FTL UTerm -> FTL UTerm
primFun = fun <=< primNotion
  where
    fun (q, Trm {trmName = TermEquality, trmArgs = [_, t]}, _)
      | not (occursH t) = return (q, t)
    fun _ = mzero


-- * Symbolic primitives

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

primCsm :: FTL a -> (SymbolPattern, [a] -> b) -> FTL b
primCsm p (pt, fm) = symbolPattern p pt >>= \l -> return $ fm l
primRsm :: FTL a -> (SymbolPattern, [a] -> t) -> FTL (a -> t)
primRsm p (pt, fm) = symbolPattern p pt >>= \l -> return $ \t -> fm $ t:l
primLsm :: FTL a -> (SymbolPattern, [a] -> t) -> FTL (a -> t)
primLsm p (pt, fm) = symbolPattern p pt >>= \l -> return $ \s -> fm $ l++[s]
primIsm :: FTL a
           -> (SymbolPattern, [a] -> t) -> FTL (a -> a -> t)
primIsm p (pt, fm) = symbolPattern p pt >>= \l -> return $ \t s -> fm $ t:l++[s]


primSnt :: FTL Formula -> FTL MNotion
primSnt p = noError $ varList >>= getExpr symbNotionExpr . snt
  where
    snt vs (pt, fm) = symbolPattern p pt >>= \l -> return (id, fm $ mkVar (VarHole ""):l, vs)


-- | Adding error reporting to pattern parsing.
patternTokenOf' :: [Text] -> FTL ()
patternTokenOf' l = label ("a word of " <> pretty_print l) $ tokenOf' l

patternSymbolTokenOf :: Text -> FTL ()
patternSymbolTokenOf l = label ("the symbol " <> pretty_print l) $ token l

-- | Most basic pattern parser: simply follow the pattern and parse terms with p
-- at variable places
predWdPattern :: FTL (b -> b, a) -> PredicatePattern -> FTL (b -> b, [a])
predWdPattern p (PredWord l : ls) = patternTokenOf' l >> predWdPattern p ls
predWdPattern p (PredVar : ls) = do
  (r, t) <- p
  (q, ts) <- predWdPattern p ls
  return (r . q, t:ts)
predWdPattern _ [] = return (id, [])

-- | Most basic pattern parser: simply follow the pattern and parse terms with p
-- at variable places
notionWdPattern :: FTL (b -> b, a) -> NotionPattern -> FTL (b -> b, [a])
notionWdPattern p (NotionWord l : ls) = patternTokenOf' l >> notionWdPattern p ls
notionWdPattern p (NotionVar : ls) = do
  (r, t) <- p
  (q, ts) <- notionWdPattern p ls
  return (r . q, t:ts)
notionWdPattern _ [] = return (id, [])
notionWdPattern _ _ = mzero

-- | Parse a symbolic pattern.
symbolPattern :: FTL a -> SymbolPattern -> FTL [a]
symbolPattern p (SymbVar : ls) = liftM2 (:) p $ symbolPattern p ls
symbolPattern p (SymbSymbol s : ls) = patternSymbolTokenOf s >> symbolPattern p ls
symbolPattern _ [] = return []

-- | Parse a multi-subject pattern: follow the pattern, but ignore the token'
-- right before the first variable. Then check that all "and" tokens have been
-- consumed. Example pattern: [Word ["commute","commutes"], Word ["with"], Vr]. Then
-- we can parse "a commutes with c and d" as well as "a and b commute".
multiPattern :: FTL (b -> b, a) -> PredicatePattern -> FTL (b -> b, [a])
multiPattern p (PredWord l : _ : PredVar : ls) = patternTokenOf' l >> predNaPattern p ls
multiPattern p (PredWord l : ls) = patternTokenOf' l >> multiPattern p ls
multiPattern _ _ = mzero


-- parses a notion: follow the pattern to the name place, record names,
-- then keep following the pattern
notionPattern :: FTL (b -> b, a)
          -> NotionPattern -> FTL (b -> b, Set PosVar, [a])
notionPattern p (NotionWord l : ls) = patternTokenOf' l >> notionPattern p ls
notionPattern p (NotionName : ls) = do
  vs <- nameList
  (q, ts) <- notionWdPattern p ls
  return (q, vs, ts)
notionPattern _ _ = mzero

-- parse an "of"-notion: follow the pattern to the notion name, then check that
-- "of" follows the name followed by a variable that is not followed by "and"
ofPattern :: FTL (b -> b, a)
          -> NotionPattern -> FTL (b -> b, Set PosVar, [a])
ofPattern p (NotionWord l : ls) = patternTokenOf' l >> ofPattern p ls
ofPattern p (NotionName : NotionWord l : NotionVar : ls) = do
  guard $ elem "of" l; vs <- nameList
  (q, ts) <- notionNaPattern p ls
  return (q, vs, ts)
ofPattern _ _ = mzero

-- | parse a "common"-notion: basically like the above. We use the special parser
-- s for the first variable place after the "of" since we expect multiple terms
-- here. Example: A common *divisor of m and n*.
commonPattern :: FTL (b -> b, a1)
          -> FTL (b -> c, [a2])
          -> NotionPattern
          -> FTL (b -> c, Set PosVar, [a2], [a1])
commonPattern p s (NotionWord l:ls) = patternTokenOf' l >> commonPattern p s ls
commonPattern p s (NotionName : NotionWord l : NotionVar : ls) = do
  guard $ elem "of" l; vs <- nameList; patternTokenOf' l
  (r, as) <- s
  when (null $ tail as) $ fail "several objects expected for `common'"
  (q, ts) <- notionNaPattern p ls
  return (r . q, vs, as, ts)
commonPattern _ _ _ = mzero

-- an auxiliary pattern parser that checks that we are not dealing with an "and"
-- token' and then continues to follow the pattern
predNaPattern :: FTL (b -> b, a)
          -> PredicatePattern -> FTL (b -> b, [a])
predNaPattern p (PredWord l : ls) = guard ("and" `notElem` l) >> patternTokenOf' l >> predWdPattern p ls
predNaPattern p ls = predWdPattern p ls

notionNaPattern :: FTL (b -> b, a)
          -> NotionPattern -> FTL (b -> b, [a])
notionNaPattern p (NotionWord l : ls) = guard ("and" `notElem` l) >> patternTokenOf' l >> notionWdPattern p ls
notionNaPattern p ls = notionWdPattern p ls


-- * Variables

nameList :: FTL (Set PosVar)
nameList = varList -|- fmap Set.singleton hidden

varList :: FTL (Set PosVar)
varList = var `sepBy` token' "," >>= nodups

nodups :: IsVar a => [a] -> FTL (Set a)
nodups vs = do
  unless ((null :: [b] -> Bool) $ duplicateNames vs) $
    fail (make_string $ "duplicate names: " <> pretty_print vs)
  pure $ Set.fromList vs

hidden :: FTL PosVar
hidden = do
  n <- gets hiddenCount
  modify $ \st -> st {hiddenCount = n + 1}
  return (PosVar (VarHidden n) Position.none)

-- | Parse the next token as a variable (a sequence of alpha-num chars beginning with an alpha)
-- and return ('x' + the sequence) with the current position.
var :: FTL PosVar
var = do
  pos <- getPos
  v <- plainVarName <|> (greekVarName </> structVarName)
  return (PosVar (VarConstant v) pos)
  where
    plainVarName = do
      v <- satisfy $ \s -> Text.all isAlphaNum s && isAlpha (Text.head s) && (s `notElem` keywords)
      primes <- Text.concat . fmap (const "'") <$> many (symbolNotAfterSpace "'")
      return $ v <> primes
    greekVarName = do
      command <- satisfy $ \s -> (Text.head s == '\\') && (Text.tail s `elem` greek)
      primes <- Text.concat . fmap (const "'") <$> many (symbolNotAfterSpace "'")
      return $ command <> primes
    structVarName = do
      command <- satisfy $ \s -> (Text.head s == '\\') && all isAsciiLetter (Text.unpack . Text.tail $ s) && Text.isSuffixOf "var" s
      optLLx () $ components </> (notation >> optLLx () (eqComponents command))
      return command
    components = do
      symbol "{}"
      optLLx () $ do
        symbol "["
        chainLL1 notClosingBrk
        symbol "]"
    notation = symbol "!"
    eqComponents command = do
      symbol "=" <|> texCommand "coloneq"
      satisfy (== command)
      components
    notClosingBrk = tokenPrim notCl
    notCl t = let tk = showToken t in guard (tk /= "]") >> return tk

-- ** Pretyped Variables

type TVar = (Set VariableName, Formula)

primTypedVar :: FTL MNotion
primTypedVar = getExpr tvrExpr tvr
  where
    tvr (vr, nt) = do
      vs <- varList
      guard $ Set.foldr (\v b -> b && v `Set.member` vr) True $ Set.map posVarName vs
      return (id, nt, vs)


-- ** Free variables

freeVars :: IsVar a => Formula -> FTL (FV a)
freeVars f = excludeSet (free f) <$> getDecl


-- ** Declarations

-- | Produce the variables declared by a formula together with their positions.
-- As parameter we pass the already known variables.
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

--  Produce variable names declared by a formula.
declNames :: Set VariableName -> Formula -> Set VariableName
declNames vs f = fvToVarSet $ excludeSet (decl f) vs

-- | Produce the bindings in a formula in a Decl data type and take care of
-- the serial counter.
bindings :: Set VariableName -> Formula -> FTL (Set Decl)
bindings vs f = makeDecls $ fvToVarSet $ excludeSet (decl f) vs


freeOrOverlapping :: Set VariableName -> Formula -> Maybe Bytes
freeOrOverlapping vs f
    | mkVar VarSlot `occursIn` f = Just $ "too few subjects for an m-predicate " <> info
    | not (Bytes.null sbs) = Just $ "free undeclared variables: "   <> sbs <> info
    | not (Bytes.null ovl) = Just $ "overlapped variables: "        <> ovl <> info
    | otherwise      = Nothing
  where
    sbs = implode_space $ map showVar $ Set.toList $ fvToVarSet $ excludeSet (free f) vs
    ovl = implode_space $ map showVar $ Set.toList $ over vs f
    info = "\n in translation: " <> pretty_print f

    over :: Set VariableName -> Formula -> Set VariableName
    over vs (All v f) = boundVars vs (declName v) f
    over vs (Exi v f) = boundVars vs (declName v) f
    over vs f = foldF (over vs) f

    boundVars :: Set VariableName -> VariableName -> Formula -> Set VariableName
    boundVars vs v f
      | v `Set.member` vs = Set.singleton v
      | v == VarEmpty = over vs f
      | otherwise = over (Set.insert v vs) f


-- * Macro expressions

iffPhrases :: [[Text]]
iffPhrases = [
    ["iff"],
    ["if", "and", "only", "if"],
    ["when", "and", "only", "when"]
  ]

standForPhrases :: [[Text]]
standForPhrases = [
    ["denote"],
    ["stand", "for"]
  ]

-- | Keywords not allowed as variable names
keywords :: [Text]
keywords = [
    "is",
    "be",
    "are",
    "does",
    "do",
    "has",
    "have",
    "that",
    "with",
    "of",
    "having",
    "such",
    "so",
    "if",
    "iff",
    "when",
    "and",
    "or"
  ]


-- * Greek letters

greek :: [Text]
greek = lowerGreek ++ varGreek ++ upperGreek

lowerGreek :: [Text]
lowerGreek = [
    "alpha", "beta", "gamma", "delta", "epsilon", "zeta", "eta", "theta",
    "iota", "kappa", "lambda", "mu", "nu", "xi", "omicron", "pi",
    "rho", "sigma", "tau", "upsilon", "phi", "chi", "psi", "omega"
  ]

varGreek :: [Text]
varGreek = [
    "varbeta", "varepsilon", "vartheta", "varkappa", "varpi",
    "varvarpi", "varrho", "varvarrho", "varsigma", "varphi"
  ]

upperGreek :: [Text]
upperGreek = [
    "Gamma", "Delta", "Theta", "Lambda", "Xi", "Pi",
    "Sigma", "Upsilon", "Phi", "Psi", "Omega"
  ]


-- * Show function

-- | Print a variable (just for now).
showVar :: VariableName -> Bytes
showVar (VarConstant nm) = pretty_print nm
showVar nm = pretty_print nm
