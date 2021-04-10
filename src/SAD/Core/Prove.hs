{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}

{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)
  Anton Lorenzen (2020)

Prover interface: export a proof task to an external prover.
-}

module SAD.Core.Prove (RunProver(..), proveOrRetrieveCached, runProveT, verify, ProveT, ProveState(..)) where

import Control.Monad.State
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc (pretty)

import SAD.Core.SourcePos
import SAD.Data.Instr
import SAD.Core.Provers
import SAD.Core.Message (Comm, output, errorExport, Kind(..), outputReasoner)
import SAD.Core.TPTP (taskToTPTP, ExportLang(..))
import SAD.Core.Task (Task(..))
import SAD.Core.Cache

class Monad m => RunProver m where
  -- | Given a prover, a timelimit, a memorylimit and a tptp text get a prover output.
  runProver :: SourcePos -> Prover -> Maybe (String, String) -> Int -> Int -> Text -> m (Int, Text)

data Result = Success | Failure | ContradictoryAxioms | TimeOut | Cached
  deriving (Eq, Ord, Show)

parseProverOutput :: Comm m => Prover -> Int -> Bool -> Bool -> Text -> m Result
parseProverOutput (Prover _ label _ _ yes con nos ros) rc printProver isByContradiction prvout = do
  let timeout = rc == 142
  let lns = filter (not . Text.null) $ Text.lines $ prvout
      out = map (("[" <> label <> "] ") <>) lns

  when (not timeout && null lns) $ errorExport noSourcePos "No prover response"
  when printProver $
      mapM_ (output "" WRITELN noSourcePos) $ map Text.unpack out

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

export :: (RunProver m, Comm m) => SourcePos -> [Prover] -> [Instr] -> Task -> m Result
export pos [] _ _ = errorExport pos "No provers"
export pos provers@(defProver:_) instrs tsk = do
  let proverName = Text.unpack $ askArgument UseProver (Text.pack $ name defProver) instrs
  
  case filter ((==) proverName . name) provers of
    [] -> errorExport noSourcePos $ "No prover named " ++ show proverName
    (prover:_) -> do
      let printProver = askFlag Printprover False instrs
      let timeLimit = askLimit Timelimit 3 instrs
      let memoryLimit = askLimit Memorylimit 2048 instrs

      let proverServerPort = askArgument ProverServerPort Text.empty instrs
      let proverServerPassword = askArgument ProverServerPassword Text.empty instrs
      let proverServer =
            if Text.null proverServerPort || Text.null proverServerPassword then
              Nothing
            else Just (Text.unpack proverServerPort, Text.unpack proverServerPassword)

      let theory = if askFlag UseFOF False instrs then FOF else TF0
      let task = taskToTPTP theory tsk
      when (askFlag Dump False instrs) $ 
        output "" WRITELN noSourcePos (Text.unpack task)

      (rc, out) <- runProver pos prover proverServer timeLimit memoryLimit task
      parseProverOutput prover rc printProver (byContradiction tsk) out

data ProveState = ProveState
  { proveGoalsFailed :: [Task]
  , proveGoalsTimeout :: [Task]
  , proveGoalsSentToATP :: !Int
  , proveGoalsCached :: !Int
  , proveCache :: Cache
  , proveFirstContradiction :: Maybe Task
  , proveProvers :: [Prover]
  , proveInstrs :: [Instr]
  } deriving (Eq, Ord, Show)

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
    provers <- proveProvers <$> get
    instrs <- proveInstrs <$> get
    modify $ \s -> s { proveGoalsSentToATP = proveGoalsSentToATP s + 1 }
    let conj = show (pretty (conjecture t))
    lift $ outputReasoner WRITELN (taskPos t)
      $ "[" <> (Text.unpack $ taskName t) <> "] " <> conj <> "\n"
    res <- lift $ export (taskPos t) provers instrs t
    case res of
      Success -> do
        modify $ \s -> s { proveCache = cache t (proveCache s) }
        pure Success
      Failure -> do
        modify $ \s -> s { proveGoalsFailed = proveGoalsFailed s ++ [t] }
        pure Failure
      ContradictoryAxioms -> do
        modify $ \s -> s { proveFirstContradiction = case proveFirstContradiction s of Nothing -> Just t; j -> j }
        pure ContradictoryAxioms
      TimeOut -> do
        modify $ \s -> s { proveGoalsTimeout = proveGoalsTimeout s ++ [t] }
        pure TimeOut
      Cached -> error $ "proveOrRetrieveCached: Can't happen"

runProveT :: (CacheStorage m) => [Prover] -> [Instr] -> ProveT m a -> m (a, ProveState)
runProveT provers instrs (ProveT p) = do
  (a, s) <- runStateT p (ProveState [] [] 0 0 mempty Nothing provers instrs)
  store $ proveCache s
  pure (a, s)

verify :: (RunProver m, Comm m, CacheStorage m) => [Task] -> ProveT m ()
verify tsks = mapM_ proveOrRetrieveCached tsks