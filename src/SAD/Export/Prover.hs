{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018, 2021)

Prover interface: export a proof task to an external prover.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.Prover (Cache, init_cache, prune_cache, export)
where

import Control.Monad (when)
import Control.Exception (SomeException, try, throw)
import Data.Maybe (fromJust, isNothing)

import qualified Isabelle.Isabelle_Thread as Isabelle_Thread
import qualified Isabelle.Position as Position
import qualified Isabelle.Time as Time
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Bytes as Bytes
import qualified Isabelle.Markup as Markup
import qualified Isabelle.Process_Result as Process_Result
import qualified Isabelle.Cache as Cache
import Isabelle.Library

import SAD.Data.Instr
import SAD.Data.Text.Context (Context, branch)
import qualified SAD.Data.Text.Block as Block

import qualified SAD.Core.Message as Message
import qualified SAD.Export.TPTP as TPTP
import qualified SAD.Data.Formula.HOL as HOL

import qualified Naproche.Program as Program
import qualified Naproche.Prover as Prover


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


  let task = make_bytes $ TPTP.output context goal
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