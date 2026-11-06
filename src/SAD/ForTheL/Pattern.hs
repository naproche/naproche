{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- |
-- Module      : SAD.ForTheL.Pattern
-- Description : Pattern parsing and pattern state management.
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
module SAD.ForTheL.Pattern (
  predicatePattern,
  namedNotionPattern,
  unnamedNotionPattern,
  symbolPatternHead,
  symbolPatternTail,
  unknownAlpha,
  slexem,
  unknownAlphaNum,
  knownVariable,
  addExpr,
  singleLetterVariable,
) where


import Control.Monad
import Control.Monad.State.Class (gets, put)

import Data.List
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text

import SAD.Data.Formula
import SAD.Data.Pattern
import SAD.ForTheL.Base
import SAD.Parser.Char (isAsciiAlphaNum, isAsciiLetter)
import SAD.Parser.Combinators
import SAD.Parser.Primitives
import SAD.Parser.Token


-- add expressions to the state of ForTheL

giveId :: Bool -> Int -> Formula -> Formula
giveId p n t = t {trId = if p then specialId n else trmId t}

incId :: Enum p => Bool -> p -> p
incId p n = if p then succ n else n

addExpr :: Formula -> Formula -> Bool -> FState -> FTL Formula

addExpr t@Trm{trmName = TermUnaryAdjective _, trmArgs = vs} f p st
  = put ns >> return nf
  where
    n = idCount st
    (pt, nf) = extractPredPattern st (giveId p n t) f
    fm = substs nf $ map varName vs
    ns = st { adjectiveExpr = (pt, fm) : adjectiveExpr st, idCount = incId p n}

addExpr t@Trm{trmName = TermUnaryVerb _, trmArgs = vs} f p st
  = put ns >> return nf
  where
    n = idCount st
    (pt, nf) = extractPredPattern st (giveId p n t) f
    fm = substs nf $ map varName vs
    ns = st {verbExpr = (pt, fm) : verbExpr st, idCount = incId p n}

addExpr t@Trm{trmName = TermMultiAdjective _, trmArgs = vs} f p st
  = put ns >> return nf
  where
    n = idCount st
    (hp:tp, nf) = extractPredPattern st (giveId p n t) f
    pt = hp : PredWord [] : PredVar : tp
    fm = substs nf $ map varName vs
    ns = st {adjectiveExpr = (pt, fm) : adjectiveExpr st, idCount = incId p n}

addExpr t@Trm{trmName = TermMultiVerb _, trmArgs = vs} f p st
  = put ns >> return nf
  where
    n = idCount st
    (hp:tp, nf) = extractPredPattern st (giveId p n t) f
    pt = hp : PredWord [] : PredVar : tp
    fm = substs nf $ map varName vs
    ns = st {verbExpr = (pt, fm) : verbExpr st, idCount = incId p n}

addExpr t@Trm{trmName = TermNotion _, trmArgs = vs} f p st
  = put ns >> return nf
  where
    n = idCount st
    (pt, nf) = extractNotionPattern st (giveId p n t) f
    fm = substs nf $ map varName vs
    ns = st {notionExpr = (pt, fm) : notionExpr st, idCount = incId p n}

addExpr Trm{trmName= TermEquality, trmArgs = [v, t@Trm {trmName = TermNotion rs}]} f p st
  = put ns >> return nf
  where
    n = idCount st
    vs = trmArgs t
    (pt, nf) = extractNotionPattern st (giveId p n t {trmName = TermThe rs}) f
    fm = substs nf $ map varName (v:vs)
    ns = st {notionExpr = (pt, fm) : notionExpr st, idCount = incId p n}

addExpr Trm{trmName = TermEquality, trmArgs = [_, t]} eq@Trm {trmName = TermEquality} p st =
  put nn >> return (mkEquality v nf)
  where
    [v, f] = trmArgs eq
    vs = trmArgs t
    n = idCount st
    (pt, nf) = extractSymbPattern (giveId p n t) f
    fm = substs nf $ map varName vs
    -- classification of pattern
    csm = lsm && rsm
    lsm = notVr (head pt)
    rsm = notVr (last pt)
    notVr SymbVar = False
    notVr _ = True
    -- add to the right category
    ns | csm = st {cfnExpr = (pt, fm) : cfnExpr st}
       | lsm = st {lfnExpr = (init pt, fm) : lfnExpr st}
       | rsm = st {rfnExpr = (tail pt, fm) : rfnExpr st}
       | otherwise = st {ifnExpr = (init (tail pt), fm) : ifnExpr st}
    -- increment id counter
    nn = ns {idCount = incId p n}

addExpr t@Trm{trmName = s, trmArgs = vs} f p st =
  put nn >> return nf
  where
    n = idCount st
    (pt, nf) = extractSymbPattern (giveId p n t) f
    fm = substs nf $ map varName vs
    -- classification of pattern
    csm = lsm && rsm
    lsm = notVr (head pt)
    rsm = notVr (last pt)
    notVr SymbVar = False
    notVr _ = True
    -- add the pattern to the right category
    ns | csm = st {cprExpr = (pt, fm) : cprExpr st}
       | lsm = st {lprExpr = (init pt, fm) : lprExpr st}
       | rsm = st {rprExpr = (tail pt, fm) : rprExpr st}
       | otherwise = st {iprExpr = (init (tail pt), fm) : iprExpr st}
    -- check if pattern is a symbolic notion
    snt = not lsm && elem (varName $ head vs) (declNames mempty nf)
    -- and add it there as well if so (and increment id counter)
    nn | snt = ns {symbNotionExpr = (tail pt,fm) : symbNotionExpr st, idCount = incId p n}
       | otherwise = ns {idCount = incId p n}






-- pattern extraction

extractPredPattern :: FState -> Formula -> Formula -> (PredicatePattern, Formula)
extractPredPattern st t@Trm {trmName = tn, trmArgs = vs} f =
  case tn of
    TermUnaryAdjective s -> (pt s, nf)
    TermMultiAdjective s -> (pt s, nf)
    TermUnaryVerb s -> (pt s, nf)
    TermMultiVerb s -> (pt s, nf)
  where
    pt = map (addPredSynonyms st)
    nf = replace t t {trId = NewId} f

extractNotionPattern :: FState -> Formula -> Formula -> (NotionPattern, Formula)
extractNotionPattern st t@Trm {trmName = tn, trmArgs = vs} f =
  case tn of
    TermNotion s -> (pt s, nf)
    TermThe s -> (pt s, nf)
  where
    pt = map (addNotionSynonyms st)
    nf = replace t t {trId = NewId} f

extractSymbPattern :: Formula -> Formula -> (SymbolPattern, Formula)
extractSymbPattern t@Trm {trmName = TermSymbolic s, trmArgs = vs} f = (s, nf)
  where
    nf = replace t t {trId = NewId} f

getSynonyms :: FState -> Text -> [Text]
getSynonyms st word =
  let dictionary = strSyms st
  in foldl' union [word] $ filter (elem word) dictionary

addPredSynonyms :: FState -> PredicatePatternComp -> PredicatePatternComp
addPredSynonyms st (PredWord words) = PredWord $ concatMap (getSynonyms st) words
addPredSynonyms _ p = p

addNotionSynonyms :: FState -> NotionPatternComp -> NotionPatternComp
addNotionSynonyms st (NotionWord words) = NotionWord $ concatMap (getSynonyms st) words
addNotionSynonyms _ p = p

-- * Pattern Parsing

-- ** Predicate Patterns

predicatePattern :: FTL PosVar -> FTL (PredicatePattern, [PosVar])
predicatePattern tvr = do
  l <- map (PredWord . singleton) <$> chain unknownAlpha
  (ls, vs) <- opt ([], []) $ predPatTail tvr
  return (l ++ ls, vs)

predPatTail :: FTL PosVar -> FTL (PredicatePattern, [PosVar])
predPatTail tvr = do
  v <- tvr
  (ls, vs) <- opt ([], []) $ predicatePattern tvr
  return (PredVar : ls, v:vs)


-- ** Notion Patterns

notionPatHead :: FTL PosVar -> FTL (NotionPattern, [PosVar])
notionPatHead tvr = do
  l <- map (NotionWord . singleton) <$> chain unknownAlpha
  (ls, vs) <- opt ([], []) $ notionPatTail tvr
  return (l ++ ls, vs)

notionPatTail :: FTL PosVar -> FTL (NotionPattern, [PosVar])
notionPatTail tvr = do
  v <- tvr
  (ls, vs) <- opt ([], []) $ notionPatHead tvr
  return (NotionVar : ls, v:vs)

namedNotionPattern :: FTL PosVar -> FTL (NotionPattern, [PosVar])
namedNotionPattern tvr = do
  l <- map (NotionWord . singleton) <$> chain unknownAlpha
  n <- nam
  (ls, vs) <- opt ([], []) $ notionPatHead tvr
  return (l ++ [NotionVar] ++ ls, n:vs)
  where
    nam :: FTL PosVar
    nam = do
      n <- fmap (const Nothing) knownVariable </> fmap Just singleLetterVariable
      case n of
        Nothing -> fail "ForTheL.Pattern.patName: name already exists"
        Just a -> pure a


unnamedNotionPattern :: FTL PosVar -> FTL (NotionPattern, [PosVar])
unnamedNotionPattern tvr = do
  l <- map (NotionWord. singleton) <$> chain unknownAlpha
  n <- hidden
  (ls, vs) <- opt ([], []) $ patShort tvr
  return (l ++ [NotionName] ++ ls, n : vs)
  where
    --patShort is a kind of buffer that ensures that a variable does not directly
    --follow the name of the notion
    patShort tvr = do
      l <- NotionWord . singleton <$> unknownAlpha
      (ls, vs) <- notionPatTail tvr
      return (l : ls, vs)


-- ** Symbol Patterns

symbolPatternHead :: FTL PosVar -> FTL (SymbolPattern, [PosVar])
symbolPatternHead tvr = do
  l <- map SymbSymbol <$> chain slexem
  (ls, vs) <- opt ([], []) $ symbolPatternTail tvr
  return (l ++ ls, vs)

symbolPatternTail :: FTL PosVar -> FTL (SymbolPattern, [PosVar])
symbolPatternTail tvr = do
  v <- tvr
  (ls, vs) <- opt ([], []) $ symbolPatternHead tvr
  return (SymbVar : ls, v:vs)


-- In-pattern lexemes and variables

unknownAlpha :: FTL Text
unknownAlpha = do
  l <- unknownAlphaNum
  guard $ Text.all isAsciiLetter l
  return $ Text.toCaseFold l

slexem :: FTL Text
slexem = symb -|- unknownAlphaNum

-- | TODO: Remove reliance on tokenPrim and then make tokenPrim private in Parser.Primitives.
-- | TODO: This should check that the variable is in math mode instead of checking against a blacklist of short words.
unknownAlphaNum :: FTL Text
unknownAlphaNum = failing knownVariable >> tokenPrim isWord
  where
    isWord t =
      let tk = showToken t
          ltk = Text.toCaseFold tk
      in guard (Text.all isAsciiAlphaNum tk && ltk `Set.notMember` keylist) >> return tk
    keylist = Set.fromList ["a","an","the","is","are","be"]

knownVariable :: FTL PosVar
knownVariable = do
  v <- var
  dvs <- getDecl
  tvs <- gets tvrExpr
  guard $ posVarName v `elem` dvs || any (elem (posVarName v) . fst) tvs
  return v

singleLetterVariable :: FTL PosVar
singleLetterVariable = do
  v <- var
  guard $ isSingleLetter $ deVar $ posVarName v
  return v
  where
    deVar (VarConstant s) = s
    deVar _ = error "Other variable"
    isSingleLetter :: Text -> Bool
    isSingleLetter x = Text.null (Text.tail x) || isTexVarName x || "var" `Text.isSuffixOf` x
    isTexVarName s = Text.head s == '\\' && all isAsciiLetter (Text.unpack . Text.tail $ s)
