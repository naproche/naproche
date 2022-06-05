{- generated by Isabelle -}

{-  Title:      Isabelle/Cache.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Cache for slow computations.
-}

module Isabelle.Cache (
  T, init, apply, prune
)
where

import Prelude hiding (init)
import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.List as List

import Isabelle.Time (Time)
import qualified Isabelle.Time as Time


data Entry v = Entry {_value :: v, _access :: Time, _timing :: Time}

newtype T k v = Cache (IORef (Map k (Entry v)))

init :: IO (T k v)
init = Cache <$> newIORef Map.empty

commit :: Ord k => T k v -> k -> Entry v -> IO v
commit (Cache ref) x e = do
  atomicModifyIORef' ref (\entries ->
    let
      entry =
        case Map.lookup x entries of
          Just e' | _access e' > _access e -> e'
          _ -> e
    in (Map.insert x entry entries, _value entry))

apply :: Ord k => T k v -> k -> IO v -> IO v
apply cache@(Cache ref) x body = do
  start <- Time.now
  entries <- readIORef ref
  case Map.lookup x entries of
    Just entry -> do
      commit cache x (entry {_access = start})
    Nothing -> do
      y <- body
      stop <- Time.now
      commit cache x (Entry y start (stop - start))

prune :: Ord k => T k v -> Int -> Time -> IO ()
prune (Cache ref) max_size min_timing = do
  atomicModifyIORef' ref (\entries ->
    let
      trim x e = if _timing e < min_timing then Map.delete x else id
      sort = List.sortBy (\(_, e1) (_, e2) -> compare (_access e2) (_access e1))
      entries1 = Map.foldrWithKey trim entries entries
      entries2 =
        if Map.size entries1 <= max_size then entries1
        else Map.fromList $ List.take max_size $ sort $ Map.toList entries1
    in (entries2, ()))