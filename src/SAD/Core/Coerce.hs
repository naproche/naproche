module SAD.Core.Coerce 
  (Coercions, add, coercibleTo, coerce) 
  where

import Prelude hiding (pred)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.List as List

-- | We store a dynamic transitive closure of the graph of coercions.
-- For n types and m coercions we can construct the data-structure in
-- time O(nm log(n)) and lookup in O(log n).
-- It was taught in the course 'New Network Flow Algorithms' in SS2020.
-- G. Italiano: Amortized efficiency of a path retrieval data structure. Theoretical Computer Science 48 (1986), 273-281

data Arborescence a = Arb (Map a (Set a))
  deriving (Eq, Ord, Show)

instance Ord a => Semigroup (Arborescence a) where
  (Arb m1) <> (Arb m2) = Arb (Map.unionWith (<>) m1 m2)

instance Ord a => Monoid (Arborescence a) where
  mempty = Arb mempty

fromRoot :: Ord a => a -> Arborescence a
fromRoot a = Arb (Map.singleton a mempty)

insert :: Ord a => (a, a) -> Arborescence a -> Arborescence a
insert (u, v) (Arb m) = Arb $ Map.insertWith (<>) v mempty 
  $ Map.adjust (Set.insert v) u m

childrenIn :: Ord a => a -> Arborescence a -> Set a
childrenIn a (Arb m) = m Map.! a

data Transitive a = Transitive
  { m :: Map (a, a) a
  , a :: Map a (Arborescence a) 
  , v :: Set a
  } deriving (Eq, Ord, Show)

instance Ord a => Semigroup (Transitive a) where
  c <> (Transitive m2 _ _) = Set.foldr' addEdge c $ Map.keysSet m2

instance Ord a => Monoid (Transitive a) where
  mempty = Transitive mempty mempty mempty

member :: Ord a => (a, a) -> Transitive a -> Bool
member e (Transitive m _ _) = e `Map.member` m

notMember :: Ord a => (a, a) -> Transitive a -> Bool
notMember e c = not $ e `member` c

pred :: Ord a => (a, a) -> Transitive a -> Maybe a
pred (i, j) (Transitive m _ _) = Map.lookup (i, j) m

addEdge :: Ord a => (a, a) -> Transitive a -> Transitive a
addEdge (i, j) c
  | (i, j) `member` c = c
  | otherwise =
    let c' = addNodes c in Set.foldr' (\x -> meld x j i j) c'
    $ Set.filter (\x -> (x, i) `member` c' && (x, j) `notMember` c') (v c')
  where
    addNodes (Transitive m a v) = Transitive { 
      m = Map.insert (i,i) i $ Map.insert (j, j) j m,
      a = Map.insertWith (<>) i (fromRoot i) $ Map.insertWith (<>) j (fromRoot j) a,
      v = Set.insert i $ Set.insert j v }

meld :: Ord a => a -> a -> a -> a -> Transitive a -> Transitive a
meld x j u v (Transitive m a v') =
  let c = Transitive (Map.insert (x, v) u m) 
                    (Map.adjust (insert (u, v)) x a) 
                    v'
  in Set.foldr' (\w -> meld x j v w) c
     $ Set.filter (\w -> (x, w) `notMember` c) $ v `childrenIn` (a Map.! j)

-- | 'Coercions' stores a preorder on 'a' with edge labels given as 'c'.
-- Once you added m relations for n elements, you can query in time O(log(n)) whether
-- two elements are related and you can get the list of those P relations 
-- that transitively relate this elements in O(P log(n)).
-- Note that the path returned is the one first added
-- and not necessarily the shortest.
-- Total memory consumption is O(nm log(n))
data Coercions a c = Coercions
  { transitive :: Transitive a
  , coercions :: Map (a, a) c
  } deriving (Eq, Ord, Show)

-- | We do not check for disjointness and simply merge.
-- Prefers the left argument on duplicates.
-- TODO: Reverse a <> a' so that we have nice addition behaviour?
instance Ord a => Semigroup (Coercions a c) where
  (<>) (Coercions a c) (Coercions a' c') = Coercions (a <> a') (c <> c')

instance Ord a => Monoid (Coercions a c) where
  mempty = Coercions mempty mempty

add :: Ord a => (a, a) -> c -> Coercions a c -> Coercions a c
add ij c (Coercions tr coe) = Coercions
  { transitive = addEdge ij tr
  , coercions = Map.insert ij c coe
  }

coercibleTo :: Ord a => (a, a) -> Coercions a c -> Bool
coercibleTo (i, j) coe
  | i == j = True
  | otherwise = member (i, j) $ transitive coe

-- | Get the list of coercions relating the elements. 
-- for (i, j) it will be in reverse order: (b, j), (a, b), (i, a)
coerce :: Ord a => (a, a) -> Coercions a c -> Maybe [c]
coerce (i, j) (Coercions tr coe)
  | i == j = Just []
  | otherwise = emptyToNothing $ map (coe Map.!)
    $ List.unfoldr (\b -> case pred (i, b) tr of
      Nothing -> Nothing
      Just p -> if i == b then Nothing else Just ((p, b), p)) j
    where emptyToNothing xs = if null xs then Nothing else Just xs