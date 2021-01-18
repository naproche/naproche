{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)
  Anton Lorenzen (2020)

Prover interface: export a proof task to an external prover.
-}

module SAD.Core.Prove (RunProver(..), verify) where

import Control.Monad (when, unless, foldM)
import SAD.Core.SourcePos
import SAD.Data.Instr
import SAD.Core.Provers
import SAD.Core.Logging
import SAD.Core.Pretty

import Data.Text (Text)
import qualified Data.Text as Text
import SAD.Core.Message (Comm, output, errorExport, Kind(..), outputReasoner, outputMain)
import SAD.Core.TPTP (tptp)
import SAD.Core.Task (Task(..))
import SAD.Core.Cache

class Monad m => RunProver m where
  -- | Given a prover, a timelimit and a tptp text get a prover output.
  runProver :: Prover -> Int -> Text -> m Text

data Result = Success | Failure | TooLittleTime | ContradictoryAxioms
  deriving (Eq, Ord, Show)

parseProverOutput :: Comm m => Prover -> Bool -> Bool -> Text -> m Result
parseProverOutput (Prover _ label _ _ yes con nos uns) printProver isByContradiction prvout = do
  let lns = filter (not . Text.null) $ Text.lines $ prvout
      out = map (("[" <> label <> "] ") <>) lns

  when (null lns) $ errorExport noSourcePos "No prover response"
  when printProver $
      mapM_ (output "" WRITELN noSourcePos) $ map Text.unpack out

  let contradictions = any (\l -> any (`Text.isPrefixOf` l) con) lns
      positive = any (\l -> any (`Text.isPrefixOf` l) yes) lns
      negative = any (\l -> any (`Text.isPrefixOf` l) nos) lns
      inconclusive = any (\l -> any (`Text.isPrefixOf` l) uns) lns

  unless (positive || contradictions || negative || inconclusive) $
      errorExport noSourcePos $ unlines ("Bad prover response:" : map Text.unpack lns)

  if | positive || (isByContradiction && contradictions) -> pure Success
     | negative -> pure Failure
     | not isByContradiction && contradictions -> pure ContradictoryAxioms
     | otherwise -> pure TooLittleTime

verify :: (RunProver m, Comm m, CacheStorage m) => 
  [Prover] -> [Instr] -> RState -> [Task] -> m RState
verify provers instrs rstate tsks = do
  (c, res) <- foldM go (mempty, addCounter Goals (length tsks) rstate) tsks
  store c
  pure res
  where
    addCounter c n s = s { trackers = trackers s ++ [Counter c n] }
    go (c, rstate) t = do
      c <- loadFile (taskFile t) c
      if isCached t c then do
        outputReasoner WRITELN noSourcePos $ Text.unpack 
          $ "Cached: [" <> (taskName t) <> "] " <> pretty (conjecture t)
        pure (cache t c, addCounter CachedCounter 1 rstate)
      else do 
        outputReasoner WRITELN noSourcePos $ Text.unpack 
          $ "[" <> (taskName t) <> "] " <> pretty (conjecture t)
        res <- export provers instrs t
        case res of
          Success -> pure (cache t c, addCounter SuccessfulGoals 1 rstate)
          Failure -> pure (c, addCounter FailedGoals 1 rstate)
          TooLittleTime -> pure (c, addCounter FailedGoals 1 rstate)
          ContradictoryAxioms -> do 
            outputMain WARNING noSourcePos 
              $ "\nFound a contradiction in the axioms! "
              <> "\nThis either means that you have introduced some axioms that are "
              <> "inconsistent or that you are in a proof by contradiction"
              <> "\n(and you should make sure to actually write 'Proof by contradiction.')"
            pure (c, addCounter FailedGoals 1 rstate)

export :: (RunProver m, Comm m) => [Prover] -> [Instr] -> Task -> m Result
export [] _ _ = errorExport noSourcePos "No provers"
export provers@(defProver:_) instrs tsk = do
  let proverName = Text.unpack $ askArgument UseProver (Text.pack $ name defProver) instrs
  
  case filter ((==) proverName . name) provers of
    [] -> errorExport noSourcePos $ "No prover named " ++ show proverName
    (prover:_) -> do
      let printProver = askFlag Printprover False instrs
      let timeLimit = askLimit Timelimit 3 instrs
      let task = tptp tsk
      when (askFlag Dump False instrs) $ 
        output "" WRITELN noSourcePos (Text.unpack task)

      out <- runProver prover timeLimit task
      parseProverOutput prover printProver (byContradiction tsk) out