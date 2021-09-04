{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)
--     Anton Lorenzen (2020)

-- Prover interface: export a proof task to an external prover.
-- TODO: use the hints to guide the prover.
-- This is section 4.5 of the eprover manual.

module SAD.Core.Prove (ProveArgs(..), RunProver(..), proveOrRetrieveCached, runProveT, verify, ProveT, ProveState(..)) where

import Control.Applicative
import Control.Monad.State
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc (pretty)

import SAD.Data.SourcePos
import SAD.Core.Provers
import SAD.Data.Message (Comm, output, errorExport, Kind(..), outputReasoner)
import SAD.Core.TPTP (taskToTPTP)
import SAD.Core.Task (Task(..))
import SAD.Core.Cache

data ProveArgs = ProveArgs
  { timelimit :: Int
  , memorylimit :: Int
  , prover :: String
  , dump :: Bool
  , noPrintGoal :: Bool
  , abortOnFail :: Bool
  , checkConsistency :: Bool
  } deriving (Eq, Ord, Show)

class Monad m => RunProver m where
  -- | Given a prover, a timelimit, a memorylimit and a tptp text get a prover output.
  runProver :: SourcePos -> Prover -> Int -> Int -> Text -> m (Int, Text)

data Result = Success | Failure | ContradictoryAxioms | TimeOut | Cached
  deriving (Eq, Ord, Show)

parseProverOutput :: Comm m => Prover -> Int -> Bool -> Text -> m Result
parseProverOutput (Prover _ _ _ _ yes con nos ros) rc isByContradiction prvout = do
  let timeout = rc == 142
  let lns = filter (not . Text.null) $ Text.lines $ prvout

  when (not timeout && null lns) $ errorExport noSourcePos "No prover response"

  let contradictions = any (\l -> any (`Text.isPrefixOf` l) con) lns
      positive = any (\l -> any (`Text.isPrefixOf` l) yes) lns
      negative = any (\l -> any (`Text.isPrefixOf` l) nos) lns
      resourceOut = any (\l -> any (`Text.isPrefixOf` l) ros) lns

  if | positive || (isByContradiction && contradictions) -> pure Success
     | negative -> pure Failure
     | not isByContradiction && contradictions -> pure ContradictoryAxioms
     | timeout || resourceOut -> pure TimeOut
     | otherwise -> errorExport noSourcePos $
          unlines ("Bad prover response:" : map Text.unpack lns)

export :: (RunProver m, Comm m) => SourcePos -> [Prover] -> ProveArgs -> Task -> m Result
export pos [] _ _ = errorExport pos "No provers"
export pos provers instrs tsk = do
  let proverName = prover instrs

  case filter ((==) proverName . name) provers of
    [] -> errorExport noSourcePos $ "No prover named " ++ show proverName
    (prover:_) -> do
      let task = taskToTPTP (exportLang prover) tsk
      when (dump instrs) $
        output "" WRITELN noSourcePos (Text.unpack task)

      (rc, out) <- runProver pos prover (timelimit instrs) (memorylimit instrs) task
      parseProverOutput prover rc (byContradiction tsk) out

data ProveState = ProveState
  { proveGoalsFailed :: [Task]
  , proveGoalsTimeout :: [Task]
  , proveGoalsSentToATP :: !Int
  , proveGoalsCached :: !Int
  , proveCache :: Cache
  , proveFirstContradiction :: Maybe Task
  , proveInstrs :: ProveArgs
  } deriving (Eq, Ord, Show)

instance Semigroup ProveState where
  (ProveState f1 t1 s1 c1 cc1 fc1 _) <> (ProveState f2 t2 s2 c2 cc2 fc2 is2) =
    ProveState (f1 <> f2) (t1 <> t2) (s1 + s2) (c1 + c2) (cc1 <> cc2)
    (fc1 <|> fc2) is2

-- | Main prove transformer
newtype ProveT m a = ProveT (StateT ProveState m a)
  deriving (Functor, Applicative, Monad, MonadState ProveState, MonadTrans)

proveOrRetrieveCached :: (Comm m, RunProver m, CacheStorage m) => Task -> ProveT m Result
proveOrRetrieveCached t = do
  c <- proveCache <$> get
  c' <- lift $ loadFile (sourceFile $ taskPos t) c
  modify $ \s -> s { proveCache = c' }
  if isCached t c' then do
    modify $ \s -> s { proveGoalsCached = proveGoalsCached s + 1 }
    modify $ \s -> s { proveCache = cache t (proveCache s) }
    pure Cached
  else do
    instrs <- proveInstrs <$> get
    modify $ \s -> s { proveGoalsSentToATP = proveGoalsSentToATP s + 1 }
    let conj = show (pretty (conjecture t))
    unless (noPrintGoal instrs) $ do
      lift $ outputReasoner WRITELN (taskPos t)
        $ "[" <> Text.unpack (taskName t) <> "] " <> conj <> "\n"
    res <- lift $ export (taskPos t) provers instrs t
    case res of
      Success -> do
        modify $ \s -> s { proveCache = cache t (proveCache s) }
        pure Success
      Failure -> do
        modify $ \s -> s { proveGoalsFailed = proveGoalsFailed s ++ [t] }
        when (abortOnFail instrs) $ do
          lift $ errorExport (taskPos t) $ "\nGoal failed!\n  " <> conj
        pure Failure
      ContradictoryAxioms -> do
        modify $ \s -> s { proveFirstContradiction = case proveFirstContradiction s of Nothing -> Just t; j -> j }
        pure ContradictoryAxioms
      TimeOut -> do
        modify $ \s -> s { proveGoalsTimeout = proveGoalsTimeout s ++ [t] }
        pure TimeOut
      Cached -> lift $ errorExport noSourcePos $ "proveOrRetrieveCached: Can't happen"

runProveT :: (CacheStorage m) => ProveArgs -> ProveT m a -> m (a, ProveState)
runProveT instrs (ProveT p) = do
  (a, s) <- runStateT p (ProveState [] [] 0 0 mempty Nothing instrs)
  store $ proveCache s
  pure (a, s)

verify :: (RunProver m, Comm m, CacheStorage m) => [Task] -> ProveT m ()
verify tsks = mapM_ proveOrRetrieveCached tsks