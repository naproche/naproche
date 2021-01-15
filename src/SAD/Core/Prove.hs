{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)
  Anton Lorenzen (2020)

Prover interface: export a proof task to an external prover.
-}

module SAD.Core.Prove (RunProver(..), verify) where

import Control.Monad (when, unless, foldM)
import Data.Maybe
import Data.List
import System.IO
import System.IO.Error
import qualified System.Process as Process
import qualified Control.Exception as Exception
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import Data.Text (Text)
import Control.Monad.State (StateT, lift)
import Control.Monad.Reader (ReaderT)

import qualified Isabelle.File as File
import qualified Isabelle.Standard_Thread as Standard_Thread

import SAD.Core.SourcePos
import SAD.Data.Instr hiding (Prover)
import SAD.Core.Provers
import SAD.Helpers (notNull)
import SAD.Core.Logging
import SAD.Core.Task (Task(..), generateTasks)
import SAD.Core.Typed
import SAD.Core.Pretty

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Instr as Instr
import SAD.Core.TPTP (tptp)
import SAD.Core.Cache

class Monad m => RunProver m where
  -- | Given a prover and a tptp text get a result.
  runProver :: Prover -> Bool -> Text -> Bool -> Int -> m Result

instance RunProver m => RunProver (StateT s m) where
  runProver a b c d e = lift $ runProver a b c d e
instance RunProver m => RunProver (ReaderT s m) where
  runProver a b c d e = lift $ runProver a b c d e

instance RunProver IO where
  runProver (Prover _ label path args yes con nos uns) printProver task isByContradiction timeLimit = do
    Standard_Thread.expose_stopped

    let proc = (Process.proc path (map (setTimeLimit timeLimit) args))
          { Process.std_in = Process.CreatePipe
          ,  Process.std_out = Process.CreatePipe
          ,  Process.std_err = Process.CreatePipe
          ,  Process.create_group = True
          ,  Process.new_session = True}
    let process = do
          (pin, pout, perr, p) <- Process.createProcess proc
          return (fromJust pin, fromJust pout, fromJust perr, p)

    (prvin, prvout, prverr, prv) <- Exception.catch process
        (\e -> Message.errorExport noSourcePos $
          "Failed to run " ++ show path ++ ": " ++ ioeGetErrorString e)

    File.setup prvin
    File.setup prvout
    File.setup prverr

    TIO.hPutStrLn prvin task
    hClose prvin

    let terminate = do
          Process.interruptProcessGroupOf prv
          Process.waitForProcess prv
          return ()

    Standard_Thread.bracket_resource terminate $ do
      output <- hGetContents prvout
      errors <- hGetContents prverr
      let lns = filter notNull $ lines $ output ++ errors
          out = map (("[" ++ label ++ "] ") ++) lns

      when (null lns) $ Message.errorExport noSourcePos "No prover response"
      when printProver $
          mapM_ (Message.output "" Message.WRITELN noSourcePos) out

      let contradictions = any (\l -> any (`isPrefixOf` l) con) lns
          positive = any (\l -> any (`isPrefixOf` l) yes) lns
          negative = any (\l -> any (`isPrefixOf` l) nos) lns
          inconclusive = any (\l -> any (`isPrefixOf` l) uns) lns

      unless (positive || contradictions || negative || inconclusive) $
          Message.errorExport noSourcePos $ unlines ("Bad prover response:" : lns)

      hClose prverr
      Process.waitForProcess prv

      if | positive || (isByContradiction && contradictions) -> pure Success
         | negative -> pure Failure
         | not isByContradiction && contradictions -> pure ContradictoryAxioms
         | otherwise -> pure TooLittleTime

verify :: (RunProver m, Message.Comm m, CacheStorage m) => 
  [Prover] -> [Instr] -> RState -> [Statement] -> m RState
verify provers instrs rstate stmts = do
  let tsks = generateTasks stmts
  (c, res) <- foldM go (mempty, addCounter Sections (length stmts)
      $ addCounter Goals (length tsks) rstate) tsks
  store c
  pure res
  where
    addCounter c n s = s { trackers = trackers s ++ [Counter c n] }
    go (c, rstate) t = do
      c <- loadFile (taskFile t) c
      if isCached t c then do
        Message.outputReasoner Message.WRITELN noSourcePos $ Text.unpack 
          $ "Cached: [" <> (taskName t) <> "] " <> pretty (conjecture t)
        pure (cache t c, addCounter CachedCounter 1 rstate)
      else do 
        Message.outputReasoner Message.WRITELN noSourcePos $ Text.unpack 
          $ "[" <> (taskName t) <> "] " <> pretty (conjecture t)
        res <- export provers instrs t
        case res of
          Success -> pure (cache t c, addCounter SuccessfulGoals 1 rstate)
          Failure -> pure (c, addCounter FailedGoals 1 rstate)
          TooLittleTime -> pure (c, addCounter FailedGoals 1 rstate)
          ContradictoryAxioms -> do 
            Message.outputMain Message.WARNING noSourcePos 
              $ "\nFound a contradiction in the axioms! "
              <> "\nThis either means that you have introduced some axioms that are "
              <> "inconsistent or that you are in a proof by contradiction"
              <> "\n(and you should make sure to actually write 'Proof by contradiction.')"
            pure (c, addCounter FailedGoals 1 rstate)

export :: (RunProver m, Message.Comm m) => [Prover] -> [Instr] -> Task -> m Result
export [] _ _ = Message.errorExport noSourcePos "No provers"
export provers@(defProver:_) instrs tsk = do
  let proverName = Text.unpack $ askArgument Instr.Prover (Text.pack $ name defProver) instrs
  
  case filter ((==) proverName . name) provers of
    [] -> Message.errorExport noSourcePos $ "No prover named " ++ show proverName
    (prover:_) -> do
      let printProver = askFlag Printprover False instrs
      let timeLimit = askLimit Timelimit 3 instrs
      let task = tptp tsk
      when (askFlag Dump False instrs) $ 
        Message.output "" Message.WRITELN noSourcePos (Text.unpack task)

      runProver prover printProver task (byContradiction tsk) timeLimit

data Result = Success | Failure | TooLittleTime | ContradictoryAxioms
  deriving (Eq, Ord, Show)


setTimeLimit :: Int -> String -> String
setTimeLimit timeLimit ('%':'d':rs) = show timeLimit ++ rs
setTimeLimit timeLimit (s:rs) = s : setTimeLimit timeLimit rs
setTimeLimit _ _ = []