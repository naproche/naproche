module SAD.Core.Cache where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import System.FilePath
import System.Directory

import SAD.Core.Task

dirname :: FilePath
dirname = ".ftlcache"

-- | We allow other monads except IO to be able to use
-- this as a library in a non-IO context (for example a webinterface).
-- TODO: Make a seperate cache for each file.
class Monad m => CacheStorage m where
  readCache :: m Cache
  writeCache :: Cache -> m ()

instance CacheStorage IO where
  readCache = do 
    dir <- getAppUserDataDirectory "naproche-sad"
    createDirectoryIfMissing True dir
    ex <- doesFileExist (dir </> dirname)
    c <- if ex then read <$> readFile (dir </> dirname) else pure (Cache mempty 0)
    pure $ c { lastRun = 1 + lastRun c }
  
  writeCache c = do
    dir <- getAppUserDataDirectory "naproche-sad"
    createDirectoryIfMissing True dir
    writeFile (dir </> dirname) (show c)

-- | The cache is simply a set of hashed tasks that we know to hold.
-- To prevent excessive growth of the cache file we also store the
-- last run at which the task was used and delete those that are old.
data Cache = Cache 
  { tasks :: HashMap Task Int
  , lastRun :: Int
  } deriving (Eq, Ord, Show, Read)

-- | Is a task cached and known to be true?
isCached :: Task -> Cache -> Bool
isCached t c = t `HashMap.member` (tasks c)

-- | Cache a task
cache :: Task -> Cache -> Cache
cache t c = c { tasks = HashMap.insert t (lastRun c) (tasks c) }

-- | Remove old (>= 5 runs) entries from the cache
cleanup :: Cache -> Cache
cleanup c = c { tasks = HashMap.mapMaybe 
  (\v -> if v + 5 < lastRun c then Nothing else Just v) $ tasks c }