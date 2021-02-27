module SAD.Core.Cache
  ( CacheStorage(..), FileCache(..)
  , Cache, reloadFile, loadFile, isCached, cache, store
  ) where

import Control.Monad
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Binary

import SAD.Core.Task

-- | We allow other monads except IO to be able to use
-- this as a library in a non-IO context (for example a webinterface).
class Monad m => CacheStorage m where
  readFileCache :: FilePath -> m FileCache
  writeFileCache :: FilePath -> FileCache -> m ()

data Cache = Cache
  { perFile :: Map FilePath FileCache
  } deriving (Eq, Ord)

instance Semigroup Cache where
  (Cache p1) <> (Cache p2) = Cache (Map.unionWith (<>) p1 p2)

instance Monoid Cache where
  mempty = Cache mempty

-- | The cache is simply a set of hashed tasks that we know to hold.
-- To prevent excessive growth of the cache file we also store the
-- last run at which the task was used and delete those that are old.
data FileCache = FileCache 
  { tasks :: HashMap Task Int
  , lastRun :: !Int
  } deriving (Eq, Ord)

instance Semigroup FileCache where
  (FileCache t1 r1) <> (FileCache t2 r2) = case compare r1 r2 of
    LT -> FileCache t2 r2
    GT -> FileCache t1 r1
    EQ -> FileCache (t1 <> t2) r1

instance Monoid FileCache where
  mempty = FileCache mempty 0

instance Binary FileCache where
  put (FileCache t l) = do
    put $ HashMap.toList t
    put l
  get = do
    t <- HashMap.fromList <$> get
    l <- get
    pure $ FileCache t l

-- | Load a file into the cache even if it is already present.
-- This may overwrite elements that were cached previously.
reloadFile :: CacheStorage m => FilePath -> Cache -> m Cache
reloadFile f (Cache c) = do
  fc <- readFileCache f
  pure $ Cache $ Map.insert f fc c

-- | Load a file into the cache if it is not present.
loadFile :: CacheStorage m => FilePath -> Cache -> m Cache
loadFile f c = if f `Map.member` (perFile c)
  then pure c else reloadFile f c

-- | Is a task cached and known to be true?
isCached :: Task -> Cache -> Bool
isCached t c = case Map.lookup (taskFile t) (perFile c) of 
  Nothing -> False
  Just fc -> t `HashMap.member` (tasks fc)

-- | Cache a task
cache :: Task -> Cache -> Cache
cache t c = 
  let fc = Map.findWithDefault mempty (taskFile t) (perFile c)
      fc' = fc { tasks = HashMap.insert t (lastRun fc) (tasks fc) }
  in  c { perFile = Map.insert (taskFile t) fc' (perFile c) }

-- | Write the cache and remove old (>= 5 runs) entries from the cache
store :: CacheStorage m => Cache -> m ()
store c = do
  let fcs = Map.toList $ perFile c
  let fcs' = flip map fcs $ \(f, fc) ->
        (f, fc { tasks = HashMap.mapMaybe 
          (\v -> if v + 5 < lastRun fc then Nothing else Just v) $ tasks fc })
  forM_ fcs' $ \(f, fc) -> writeFileCache f fc