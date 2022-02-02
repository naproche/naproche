{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018, 2021)

Prover interface: export a proof task to an external prover.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.Prover (export)
where

import Control.Monad (when)
import Data.Maybe (fromJust, isNothing)
import qualified Data.Text.Lazy as Text

import qualified Isabelle.Isabelle_Thread as Isabelle_Thread
import qualified Isabelle.Position as Position
import qualified Isabelle.Time as Time
import qualified Isabelle.Bytes as Bytes
import qualified Isabelle.Process_Result as Process_Result
import Isabelle.Library

import SAD.Core.Base (reportBracketIO)
import SAD.Data.Instr hiding (Prover)
import SAD.Data.Text.Context (Context, branch)
import qualified SAD.Data.Text.Block as Block

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Instr as Instr
import qualified SAD.Export.TPTP as TPTP
import qualified SAD.Data.Formula.HOL as HOL

import qualified Naproche.Program as Program
import qualified Naproche.Prover as Prover


export :: Position.T -> Int -> [Instr] -> [Context] -> Context -> IO Prover.Status
export pos iteration instrs context goal = do
  Isabelle_Thread.expose_stopped

  program_context <- Program.thread_context
  when (Program.is_isabelle program_context) $ do
    s <- HOL.print_sequent program_context $ HOL.make_sequent context goal
    Message.outputExport Message.TRACING pos s
    return ()

  let printProver = askParam printproverParam instrs
  let timeLimit = askParam timelimitParam instrs
  let memoryLimit = askParam memorylimitParam instrs
  let byContradiction =
        elem Block.ProofByContradiction $
          map Block.kind (head (branch goal) : concatMap branch context)

  let
    proverNameDefault = Text.pack $ make_string $ Prover.get_name Prover.eprover
    proverName = askArgument Instr.Prover proverNameDefault instrs
    prover = do
      prover <- Prover.find (make_bytes proverName)
      return $
        prover
        |> Prover.timeout (Time.seconds $ fromIntegral timeLimit)
        |> Prover.memory_limit memoryLimit
        |> Prover.by_contradiction byContradiction

  when (isNothing prover) $ Message.errorExport pos ("No prover named " <> quote proverName)


  let task = make_bytes $ TPTP.output context goal
  when (askParam dumpParam instrs) $
    Message.output Bytes.empty Message.WRITELN pos task

  reportBracketIO pos $ do
    result <- Prover.run program_context (fromJust prover) task
    when printProver $
      Message.output Bytes.empty Message.WRITELN pos (Process_Result.out result)

    case Prover.status (fromJust prover) result of
      Prover.Error msg -> Message.errorExport pos msg
      status -> return status
