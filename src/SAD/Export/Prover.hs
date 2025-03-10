-- |
-- Module      : SAD.Export.Prover
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2018, 2021, Makarius Wenzel
-- License     : GPL-3
--
-- Prover interface: export a proof task to an external prover.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.Prover (
  Cache,
  init_cache,
  prune_cache,
  export
) where

import Control.Monad (when)
import Control.Exception (SomeException, try, throw)
import Data.Maybe (fromJust, isNothing)

import SAD.Data.Instr
import SAD.Data.Text.Context (Context, branch, output)
import SAD.Data.Text.Block qualified as Block
import SAD.Core.Message qualified as Message
import SAD.Data.Formula.HOL qualified as HOL

import Isabelle.Isabelle_Thread qualified as Isabelle_Thread
import Isabelle.Position qualified as Position
import Isabelle.Time qualified as Time
import Isabelle.Bytes (Bytes)
import Isabelle.Bytes qualified as Bytes
import Isabelle.Markup qualified as Markup
import Isabelle.Process_Result qualified as Process_Result
import Isabelle.Cache qualified as Cache
import Isabelle.Library

import Naproche.Program qualified as Program
import Naproche.Prover qualified as Prover


type Cache = Cache.T (Bytes, Int, Int, Bool, Bytes) Process_Result.T

init_cache :: IO Cache
init_cache = Cache.init

prune_cache :: Cache -> IO ()
prune_cache cache = Cache.prune cache 10000 (Time.ms 100)


export :: Cache -> Position.T -> Int -> [Instr] -> [Context] -> Context -> IO Prover.Status
export cache pos iteration instrs context goal = do
  Isabelle_Thread.expose_stopped

  program_context <- Program.thread_context
  when (Program.is_isabelle program_context) $ do
    s <- HOL.print_sequent program_context $ HOL.make_sequent context goal
    Message.outputExport Message.TRACING pos s
    return ()

  let printProver = getInstr printproverParam instrs
  let timeLimit = getInstr timelimitParam instrs
  let memoryLimit = getInstr memorylimitParam instrs
  let byContradiction =
        elem Block.ProofByContradiction $
          map Block.kind (head (branch goal) : concatMap branch context)

  let
    proverName = getInstr proverParam instrs
    prover = do
      prover <- Prover.find proverName
      return $
        prover
        |> Prover.timeout (Time.seconds $ fromIntegral timeLimit)
        |> Prover.memory_limit memoryLimit
        |> Prover.by_contradiction byContradiction

  when (isNothing prover) $ Message.errorExport pos ("No prover named " <> quote proverName)

  let task = make_bytes $ output context goal
  when (getInstr dumpParam instrs) $
    Message.output Bytes.empty Message.WRITELN pos task

  reportBracketIO pos $ do
    result <-
      Cache.apply cache (proverName, timeLimit, memoryLimit, byContradiction, task) $
        Prover.run program_context (fromJust prover) task
    when printProver $
      Message.output Bytes.empty Message.WRITELN pos (Process_Result.out result)

    case Prover.status (fromJust prover) result of
      Prover.Error msg -> Message.errorExport pos msg
      status -> return status


reportBracketIO :: Position.T -> IO a -> IO a
reportBracketIO pos body = do
  Message.report pos Markup.running
  (res :: Either SomeException a) <- try body
  case res of
    Left e -> do
      Message.report pos Markup.failed
      Message.report pos Markup.finished
      throw e
    Right x -> do
      Message.report pos Markup.finished
      return x
