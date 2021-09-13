{-# LANGUAGE MultiWayIf #-}
{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018, 2021)

Prover interface: export a proof task to an external prover.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.Prover where

import Control.Monad (when, unless)
import Data.List
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy (Text)

import qualified Isabelle.Isabelle_Thread as Isabelle_Thread
import qualified Isabelle.Position as Position
import qualified Isabelle.Time as Time
import qualified Isabelle.Bash as Bash
import Isabelle.Library
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Process_Result as Process_Result

import SAD.Core.Base (reportBracketIO)
import SAD.Data.Instr hiding (Prover)
import SAD.Data.Text.Context (Context, branch, formula)
import qualified SAD.Data.Text.Block as Block
import SAD.Export.Base

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Instr as Instr
import qualified SAD.Export.TPTP as TPTP
import qualified SAD.Data.Formula.HOL as HOL

import qualified Naproche.Program as Program
import qualified Naproche.System as System


export :: Position.T -> Int -> [Prover] -> [Instr] -> [Context] -> Context -> IO Result
export pos depth provers instrs context goal = do
  Isabelle_Thread.expose_stopped

  program_context <- Program.thread_context
  when (Program.is_isabelle program_context) $ do
    let asms = reverse $ map formula context
    let concl = formula goal
    _ <- HOL.cert_terms program_context (map HOL.export_formula (asms <> [concl]))
    s <- HOL.print_sequent program_context (asms, [concl])
    Message.outputExport Message.TRACING pos s
    return ()

  when (null provers) $ Message.errorExport pos ("No provers" :: Bytes)

  let proverName = Text.unpack $ askArgument Instr.Prover (Text.pack $ name $ head provers) instrs
      proversNamed = filter ((==) proverName . name) provers

  when (null proversNamed) $
    Message.errorExport pos ("No prover named " <> proverName)

  let printProver = askFlag Printprover False instrs
  let timeLimit = askLimit Timelimit 3 instrs
  let memoryLimit = askLimit Memorylimit 2048 instrs

  let task = TPTP.output context goal
  let isByContradiction = elem Block.ProofByContradiction $
        map Block.kind (head (branch goal) : concatMap branch context)

  when (askFlag Dump False instrs) $
    Message.output Bytes.empty Message.WRITELN pos task

  reportBracketIO pos $
    runProver pos (head proversNamed) printProver task isByContradiction timeLimit memoryLimit

data Result = Success | Failure | ContradictoryAxioms | Unknown | Error
  deriving (Eq, Ord, Show)

runProver :: Position.T -> Prover -> Bool -> Text -> Bool -> Int -> Int -> IO Result
runProver pos (Prover _ label path args yes con nos uns) printProver task isByContradiction timeLimit memoryLimit = do
  context <- Program.thread_context
  result <- System.bash_process context $
    Bash.script (Bash.strings (map make_bytes (path : map (setLimits timeLimit memoryLimit) args)))
    |> Bash.timeout (Time.seconds (fromIntegral timeLimit))
    |> Bash.input (make_bytes task)

  let timeout = Process_Result.rc result == Process_Result.timeout_rc
  let lns = filter (not . Bytes.null) (Process_Result.out_lines result)
  let out = map (("[" <> make_bytes label <> "] ") <>) lns

  when (not timeout && null lns) $ Message.errorExport pos ("No prover response" :: Bytes)
  when printProver $ mapM_ (Message.output Bytes.empty Message.WRITELN pos) out

  let contradictions = any (\l -> any (`isPrefixOf` make_string l) con) lns
      positive = any (\l -> any (`isPrefixOf` make_string l) yes) lns
      negative = any (\l -> any (`isPrefixOf` make_string l) nos) lns
      inconclusive = any (\l -> any (`isPrefixOf` make_string l) uns) lns

  unless (timeout || positive || contradictions || negative || inconclusive) $
      Message.errorExport pos $ cat_lines ("Bad prover response:" : lns)

  if | positive || (isByContradiction && contradictions) -> pure Success
     | negative -> pure Failure
     | not isByContradiction && contradictions -> pure ContradictoryAxioms
     | timeout -> pure Unknown
     | otherwise -> pure Error

setLimits :: Int -> Int -> String -> String
setLimits timeLimit memoryLimit = go
  where
    go ('%':'t':rs) = show timeLimit ++ go rs
    go ('%':'m':rs) = show memoryLimit ++ go rs
    go (s:rs) = s : go rs
    go [] = []