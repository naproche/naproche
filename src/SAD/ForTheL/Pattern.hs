-- |
-- Module      : SAD.ForTheL.Pattern
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Pattern parsing and pattern state management.


{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module SAD.ForTheL.Pattern (
  knownVariable,
  newPrdPattern,
  addExpr,
  unnamedNotion,
  singleLetterVariable,
  newNotionPattern
) where


import Control.Monad.State.Class (put, gets)
import Data.Set qualified as Set
import Data.List
import Data.Char (toUpper)
import Control.Applicative
import Control.Monad
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.ForTheL.Base
import SAD.Parser.Combinators
import SAD.Parser.Token
import SAD.Parser.Primitives
import SAD.Data.Formula
import SAD.Helpers


-- add expressions to the state of ForTheL

giveId :: Bool -> Int -> Formula -> Formula
giveId p n t = t {trId = if p then specialId n else (trmId t)}

incId :: Enum p => Bool -> p -> p
incId p n = if p then succ n else n

addExpr :: Formula -> Formula -> Bool -> FState -> FTL Formula

addExpr t@Trm{trmName = TermUnaryAdjective _, trmArgs = vs} f p st
  = put ns >> return nf
  where
    n = idCount st
    (pt, nf) = extractWordPattern st (giveId p n t) f
    fm  = substs nf $ map varName vs
    ns  = st { adjectiveExpr = (pt, fm) : adjectiveExpr st, idCount = incId p n}

addExpr t@Trm{trmName = TermUnaryVerb _, trmArgs = vs} f p st
  = put ns >> return nf
  where
    n = idCount st
    (pt, nf) = extractWordPattern st (giveId p n t) f
    fm = substs nf $ map varName vs
    ns = st {verbExpr = (pt, fm) : verbExpr st, idCount = incId p n}

addExpr t@Trm{trmName = TermMultiAdjective _, trmArgs = vs} f p st
  = put ns >> return nf
  where
    n = idCount st
    ((hp:tp), nf) = extractWordPattern st (giveId p n t) f
    pt = hp : Word [] : Vr : tp
    fm = substs nf $ map varName vs
    ns = st {adjectiveExpr = (pt, fm) : adjectiveExpr st, idCount = incId p n}

addExpr t@Trm{trmName = TermMultiVerb _, trmArgs = vs} f p st
  = put ns >> return nf
  where
    n = idCount st
    ((hp:tp), nf) = extractWordPattern st (giveId p n t) f
    pt = hp : Word [] : Vr : tp
    fm = substs nf $ map varName vs
    ns = st {verbExpr = (pt, fm) : verbExpr st, idCount = incId p n}

addExpr t@Trm{trmName = TermNotion _, trmArgs = vs} f p st
  = put ns >> return nf
  where
    n = idCount st
    (pt, nf) = extractWordPattern st (giveId p n t) f
    fm = substs nf $ map varName vs
    ns = st {notionExpr = (pt, fm) : notionExpr st, idCount = incId p n}

addExpr Trm{trmName= TermEquality, trmArgs = [v, t@Trm {trmName = TermNotion rs}]} f p st
  = put ns >> return nf
  where
    n = idCount st
    vs = trmArgs t
    (pt, nf) = extractWordPattern st (giveId p n t {trmName = TermThe rs}) f
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
    notVr Vr = False
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
    notVr Vr = False
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

extractWordPattern :: FState -> Formula -> Formula -> ([Pattern], Formula)
extractWordPattern st t@Trm {trmName = s, trmArgs = vs} f = (pt, nf)
  where
    pt = map getPattern ws
    nt = t {trmName = pr $ getName pt}
    nf = replace nt t {trId = NewId} f
    (pr, ws) = fmap Text.words $ termSplit s
    dict = strSyms st

    getPattern "." = Nm
    getPattern "__VAR__" = Vr
    getPattern w = Word $ foldl' union [w] $ filter (elem w) dict

    getName (Word (t:_):ls) = case Text.uncons t of
      Just (c, cs) -> Text.cons (toUpper c) cs <> getName ls
      Nothing -> getName ls
    getName (_:ls) = getName ls
    getName [] = ""


extractSymbPattern :: Formula -> Formula -> ([Pattern], Formula)
extractSymbPattern t@Trm {trmName = TermName s, trmArgs = vs} f = (pt, nf)
  where
    pt = map getPattern (Text.words s)
    nt = t {trmName = TermSymbolic $ getName pt}
    nf = replace nt t {trId = NewId} f

    getPattern "__VAR__" = Vr
    getPattern w = Symbol w

    getName (Symbol s:ls) = s <> getName ls
    getName (Vr:ls) = "." <> getName ls
    getName [] = ""




-- New patterns


newPrdPattern :: FTL PosVar -> FTL Formula
newPrdPattern tvr = multi </> unary </> newSymbPattern tvr
  where
    unary = do
      v <- tvr
      (t, vs) <- unaryAdj -|- unaryVerb
      return $ mkTrm NewId t $ map pVar (v:vs)
    multi = do
      (u,v) <- liftM2 (,) tvr (comma >> tvr)
      (t, vs) <- multiAdj -|- multiVerb
      return $ mkTrm NewId t $ map pVar (u:v:vs)

    unaryAdj = do
      is
      (t, vs) <- optInTexArg "emph" $ patHead unknownAlpha tvr
      return (TermUnaryAdjective t, vs)
    multiAdj = do
      is
      (t, vs) <- optInTexArg "emph" $ patHead unknownAlpha tvr
      return (TermMultiAdjective t, vs)
    unaryVerb = do
      (t, vs) <- optInTexArg "emph" $ patHead unknownAlpha tvr
      return (TermUnaryVerb t, vs)
    multiVerb = do
      (t, vs) <- optInTexArg "emph" $ patHead unknownAlpha tvr
      return (TermMultiVerb t, vs)

newNotionPattern :: FTL PosVar -> FTL (Formula, PosVar)
newNotionPattern tvr = (notion <|> function) </> unnamedNotion tvr
  where
    notion = do
      an
      (t, v:vs) <- optInTexArg "emph" $ patName unknownAlpha tvr
      return (mkTrm NewId (TermNotion t) $ map pVar (v:vs), v)
    function = do
      the
      (t, v:vs) <- optInTexArg "emph" $ patName unknownAlpha tvr
      return (mkEquality (pVar v) $ mkTrm NewId (TermNotion t) $ map pVar vs, v)

unnamedNotion :: FTL PosVar -> FTL (Formula, PosVar)
unnamedNotion tvr = (notion <|> function) </> (newSymbPattern tvr >>= equ)
  where
    notion = do
      an
      (t, v:vs) <- optInTexArg "emph" $ patNoName unknownAlpha tvr
      return (mkTrm NewId (TermNotion t) $ map pVar (v:vs), v)
    function = do
      the
      (t, v:vs) <- optInTexArg "emph" $ patNoName unknownAlpha tvr
      return (mkEquality (pVar v) $ mkTrm NewId (TermNotion t) $ map pVar vs, v)
    equ t = do
      v <- hidden
      return (mkEquality (pVar v) t, v)


newSymbPattern :: FTL PosVar -> FTL Formula
newSymbPattern tvr = left -|- right
  where
    left = do
      (t, vs) <- patHead slexem tvr
      return $ mkTrm NewId (TermName t) $ map pVar vs
    right = do
      (t, vs) <- patTail slexem tvr
      guard $ not $ null $ tail $ Text.words t
      return $ mkTrm NewId (TermName t) $ map pVar vs


-- pattern parsing


patHead :: FTL Text -> FTL a -> FTL (Text, [a])
patHead lxm tvr = do
  l <- Text.unwords <$> chain lxm
  (ls, vs) <- opt ("", []) $ patTail lxm tvr
  return (l <> " " <> ls, vs)


patTail :: FTL Text -> FTL a -> FTL (Text, [a])
patTail lxm tvr = do
  v <- tvr
  (ls, vs) <- opt ("", []) $ patHead lxm tvr
  return ("__VAR__ " <> ls, v:vs)


patName :: FTL Text -> FTL PosVar -> FTL (Text, [PosVar])
patName lxm tvr = do
  l <- Text.unwords <$> chain lxm
  n <- nam
  (ls, vs) <- opt ("", []) $ patHead lxm tvr
  return (l <> " . " <> ls, n:vs)
  where
    nam :: FTL PosVar
    nam = do
      n <- fmap (const Nothing) knownVariable </> fmap Just singleLetterVariable
      case n of
        Nothing -> fail "ForTheL.Pattern.patName: name already exists"
        Just a -> pure a


patNoName :: FTL Text -> FTL PosVar -> FTL (Text, [PosVar])
patNoName lxm tvr = do
  l <- Text.unwords <$> chain lxm
  n <- hidden
  (ls, vs) <- opt ("", []) $ patShort lxm tvr
  return (l <> " . " <> ls, n:vs)
  where
    --patShort is a kind of buffer that ensures that a variable does not directly
    --follow the name of the notion
    patShort lxm tvr = do
      l <- lxm
      (ls, vs) <- patTail lxm tvr
      return (l <> " " <> ls, vs)



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
    deVar _ = error "SAD.ForTheL.Pattern.singleLetterVariable: other variable"
    isSingleLetter :: Text -> Bool
    isSingleLetter x = Text.null (Text.tail x) || isTexVarName x
    isTexVarName s = Text.head s == '\\' && Text.tail s `elem` greek
