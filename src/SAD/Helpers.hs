-- |
-- Module      : SAD.Helpers
-- Copyright   : (c) 2019, Adrian De Lon,
--               (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- Helper functions.


module SAD.Helpers (
  notNull,
  nubOrd,
  nubOrdBy,
  nubOrdOn,
  isAsciiSymbol,
  isAsciiDigit,
  isAsciiLetter,
  isAsciiAlphaNum,
  isAsciiPeriod,
  parenIf
) where

import Control.Arrow
import Data.Function
import Data.Char qualified as Char


-- | Returns @False@ if the list is empty and @True@ otherwise.
notNull :: [a] -> Bool
notNull [] = False
notNull _  = True

-- nubOrds taken from the 'extra' package.

-- | /O(n log n)/. The 'nubOrd' function removes duplicate elements from a list.
-- In particular, it keeps only the first occurrence of each element.
-- Unlike the standard 'nub' operator, this version requires an 'Ord' instance
-- and consequently runs asymptotically faster.
--
-- > nubOrd "this is a test" == "this ae"
-- > nubOrd (take 4 ("this" ++ undefined)) == "this"
-- > \xs -> nubOrd xs == nub xs
nubOrd :: Ord a => [a] -> [a]
nubOrd = nubOrdBy compare

-- | A version of 'nubOrd' which operates on a portion of the value.
--
-- > nubOrdOn length ["a","test","of","this"] == ["a","test","of"]
nubOrdOn :: Ord b => (a -> b) -> [a] -> [a]
nubOrdOn f = map snd . nubOrdBy (compare `on` fst) . map (f &&& id)

-- | A version of 'nubOrd' with a custom predicate.
--
-- > nubOrdBy (compare `on` length) ["a","test","of","this"] == ["a","test","of"]
nubOrdBy :: (a -> a -> Ordering) -> [a] -> [a]
nubOrdBy cmp xs = f E xs
    where f seen [] = []
          f seen (x:xs) | memberRB cmp x seen = f seen xs
                        | otherwise = x : f (insertRB cmp x seen) xs

---------------------------------------------------------------------
-- OKASAKI RED BLACK TREE
-- Taken from https://www.cs.kent.ac.uk/people/staff/smk/redblack/Untyped.hs

data Color = R | B deriving Show
data RB a = E | T Color (RB a) a (RB a) deriving Show

{- Insertion and membership test as by Okasaki -}
insertRB :: (a -> a -> Ordering) -> a -> RB a -> RB a
insertRB cmp x s =
    T B a z b
    where
    T _ a z b = ins s
    ins E = T R E x E
    ins s@(T B a y b) = case cmp x y of
        LT -> balance (ins a) y b
        GT -> balance a y (ins b)
        EQ -> s
    ins s@(T R a y b) = case cmp x y of
        LT -> T R (ins a) y b
        GT -> T R a y (ins b)
        EQ -> s

memberRB :: (a -> a -> Ordering) -> a -> RB a -> Bool
memberRB cmp x E = False
memberRB cmp x (T _ a y b) = case cmp x y of
    LT -> memberRB cmp x a
    GT -> memberRB cmp x b
    EQ -> True

{- balance: first equation is new,
   to make it work with a weaker invariant -}
balance :: RB a -> a -> RB a -> RB a
balance (T R a x b) y (T R c z d) = T R (T B a x b) y (T B c z d)
balance (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance a x b = T B a x b


-- * Character Categories

isAsciiSymbol :: Char -> Bool
isAsciiSymbol c =
     ('\x0021' <= c && c <= '\x002F')
  || ('\x003A' <= c && c <= '\x0040')
  || ('\x005B' <= c && c <= '\x0060')
  || ('\x007B' <= c && c <= '\x007E')

isAsciiDigit :: Char -> Bool
isAsciiDigit = Char.isDigit

isAsciiLetter :: Char -> Bool
isAsciiLetter c = Char.isAsciiUpper c || Char.isAsciiLower c

isAsciiAlphaNum :: Char -> Bool
isAsciiAlphaNum c = isAsciiLetter c || isAsciiDigit c

isAsciiPeriod :: Char -> Bool
isAsciiPeriod c = c == '\x002E'


-- * String Operations

-- | Wrap a string in parentheses if a predicate holds true.
parenIf :: Bool -> String -> String
parenIf pred string = if pred then "(" ++ string ++ ")" else string
