{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Prover interface: export a proof task to an external prover.
-}

module SAD.Core.Prove where

import Control.Monad (when, unless)
import Data.Maybe
import Data.List
import System.IO
import System.IO.Error
import qualified System.Process as Process
import qualified Control.Exception as Exception
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import Data.Text (Text)

import qualified Isabelle.File as File
import qualified Isabelle.Standard_Thread as Standard_Thread

import SAD.Core.SourcePos
import SAD.Data.Instr hiding (Prover)
import qualified SAD.Data.Text.Block as Block
import SAD.Core.Provers
import SAD.Helpers (notNull)
import SAD.Data.Text.Block (Block(Block))
import SAD.Data.Text.Context (Context(..))
import SAD.Data.Formula (Formula(..))
import SAD.Core.Base
import SAD.Core.Task (Task(..), generateTasks)
import SAD.Core.Typed
import SAD.Core.Pretty

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Instr as Instr
import SAD.Core.TPTP (tptp)

verify :: [Prover] -> [Instr] -> RState -> [Statement] -> IO (Bool, RState)
verify provers instrs rstate stmts = go rstate tsks
  where
    tsks = generateTasks stmts

    addCounter c n s = s { trackers = trackers s ++ [Counter c n] }

    go rstate [] = pure (True, addCounter Sections (length stmts) 
      $ addCounter Goals (length tsks) rstate)
    go rstate (t:ts) = do
      TIO.putStrLn $ "[" <> (taskName t) <> "] " <> pretty (conjecture t)
      res <- export provers instrs t
      case res of
        Success -> go (addCounter SuccessfulGoals 1 rstate) ts
        Failure -> go (addCounter FailedGoals 1 rstate) ts
        TooLittleTime -> go (addCounter FailedGoals 1 rstate) ts
        ContradictoryAxioms -> error $ "\nFound a contradiction in the axioms! "
          <> "\nThis either means that you have introduced some axioms that are "
          <> "inconsistent or that you are in a proof by contradiction"
          <> "\n(and you should make sure to actually write 'Proof by contradiction.')"

export :: [Prover] -> [Instr] -> Task -> IO Result
export provers instrs tsk = do
  Standard_Thread.expose_stopped

  when (null provers) $ Message.errorExport noSourcePos "No provers"

  let proverName = Text.unpack $ askArgument Instr.Prover (Text.pack $ name $ head provers) instrs
      proversNamed = filter ((==) proverName . name) provers

  when (null proversNamed) $ 
    Message.errorExport noSourcePos $ "No prover named " ++ show proverName
  
  let printProver = askFlag Printprover False instrs
  let timeLimit = askLimit Timelimit 3 instrs
  let task = tptp tsk
  when (askFlag Dump False instrs) $ 
    Message.output "" Message.WRITELN noSourcePos (Text.unpack task)

  runProver (head proversNamed) printProver task (byContradiction tsk) timeLimit

data Result = Success | Failure | TooLittleTime | ContradictoryAxioms
  deriving (Eq, Ord, Show)

fromContext :: Context -> (Text, Formula)
fromContext (Context fr (Block {Block.name = m} : _)) = (m, fr)
fromContext (Context fr []) = ("", fr)

runProver :: Prover -> Bool -> Text -> Bool -> Int -> IO Result
runProver (Prover _ label path args yes con nos uns) printProver task isByContradiction timeLimit = do
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

setTimeLimit :: Int -> String -> String
setTimeLimit timeLimit ('%':'d':rs) = show timeLimit ++ rs
setTimeLimit timeLimit (s:rs) = s : setTimeLimit timeLimit rs
setTimeLimit _ _ = []