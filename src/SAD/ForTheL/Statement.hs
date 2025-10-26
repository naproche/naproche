-- |
-- Module      : SAD.ForTheL.Statement
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2025 Marcel Schütz
-- License     : GPL-3
--
-- Statements.


{-# LANGUAGE OverloadedStrings #-}

module SAD.ForTheL.Statement (
  symbolicTerm,
  sTerm,
  sVar,
  trm,
  oneArgument,
  twoArguments,
  multExi,
  conjChain,
  digadd,
  digNotion,
  single,
  dig
) where


import Data.Set (Set)
import Data.Set qualified as Set

import SAD.Data.Formula
import SAD.Data.Text.Decl
import SAD.ForTheL.Base
import SAD.Parser.Combinators
import SAD.Parser.Primitives (token')


-- * Symbolic Terms

symbolicTerm :: FTL (a -> a, Formula)
symbolicTerm = fmap ((,) id) sTerm

sTerm :: FTL Formula
sTerm = iTerm
  where
    iTerm = lTerm >>= iTl
    iTl t = opt t $ (primIfn sTerm <*> return t <*> iTerm) >>= iTl

    lTerm = rTerm -|- label "symbolic term" (primLfn sTerm <*> lTerm)

    rTerm = cTerm >>= rTl
    rTl t = opt t $ (primRfn sTerm <*> return t) >>= rTl

    cTerm = label "symbolic term" $ sVar -|- parenthesised sTerm -|- primCfn sTerm

sVar :: FTL Formula
sVar = fmap pVar var


-- * Helpers for Low-Level Functions

trm :: FTL (Formula -> p1 -> p2 -> Formula)
trm = do
  t <- sTerm; return $ \f _ _ -> mkDom f `mkEquality` t

-- | Parse a single variable
oneArgument :: FTL Formula
oneArgument = sVar

-- | Parse two variables, separated by a comma
twoArguments :: FTL Formula
twoArguments = do
  [l,r] <- symbolPattern sVar [Vr, Symbol ",", Vr]
  return $ mkPair l r


-- * Chain Tools

multExi :: Foldable t1 => [(t2 -> Formula, t2, t1 Decl)] -> Formula
multExi ((q, f, vs):ns) = foldr mbdExi (q f `blAnd` multExi ns) vs
multExi [] = Top

conjChain :: FTL Formula -> FTL Formula
conjChain = fmap (foldl1 And) . flip sepBy (token' "and")



-- * Digger

digadd :: (a, Formula, c) -> (a, Formula, c)
digadd (q, f, v) = (q, Tag Dig f, v)

digNotion :: (a, Formula, Set PosVar) -> FTL (a, Formula, Set PosVar)
digNotion (q, f, v) = dig f (map pVar $ Set.toList v) >>= \ g -> return (q, g, v)

single :: (a, b, Set c) -> FTL (a, b, c)
single (q, f, vs) = case Set.elems vs of
  [v] -> return (q, f, v)
  _   -> fail "inadmissible multinamed notion"

dig :: Formula -> [Formula] -> FTL Formula
dig f [_] | occursS f = fail "too few subjects for an m-predicate"
dig f ts = return (dive f)
  where
    dive :: Formula -> Formula
    dive (Tag Dig f) = down digS f
    dive (Tag DigMultiSubject f) = down (digM $ zip ts $ tail ts) f
    dive (Tag DigMultiPairwise f) = down (digM $ pairs ts) f
    dive f | isTrm f = f
    dive f = mapF dive f

    down :: (Formula -> [Formula]) -> Formula -> Formula
    down fn (And f g) = And (down fn f) (down fn g)
    down fn f = foldl1 And (fn f)

    digS :: Formula -> [Formula]
    digS f
      | occursH f = map (\t -> subst t (VarHole "") f) ts
      | otherwise = [f]

    digM :: [(Formula, Formula)] -> Formula -> [Formula]
    digM ps f
      | not (occursS f) = digS f
      | not (occursH f) = map (\t -> subst t VarSlot f) $ tail ts
      | otherwise = map (\ (x,y) -> subst y VarSlot $ subst x (VarHole "") f) ps

-- Example:
-- pairs [1,2,3,4]
-- [(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
pairs :: [a] -> [(a, a)]
pairs (t:ts) = [ (t, s) | s <- ts ] ++ pairs ts
pairs _ = []
