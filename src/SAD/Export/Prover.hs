{-# LANGUAGE MultiWayIf #-}
{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Prover interface: export a proof task to an external prover.
-}

module SAD.Export.Prover where

import Control.Monad (when, unless)
import Data.Maybe
import Data.List
import System.IO
import System.IO.Error
import System.Exit (ExitCode(..))
import qualified System.Process as Process
import qualified Control.Exception as Exception
import qualified Data.ByteString as ByteString
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as TIO
import Data.Text.Lazy (Text)

import qualified Isabelle.Isabelle_Thread as Isabelle_Thread
import qualified Isabelle.Server as Server
import qualified Isabelle.XML as XML
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Value as Value
import qualified Isabelle.Naproche as Naproche
import Isabelle.Library (make_bytes, make_string)
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.UTF8 as UTF8

import SAD.Core.SourcePos
import SAD.Core.Base (reportBracketIO)
import SAD.Data.Instr hiding (Prover)
import SAD.Data.Text.Context (Context, branch)
import qualified SAD.Data.Text.Block as Block
import SAD.Export.Base
import SAD.Helpers (notNull)

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Instr as Instr
import qualified SAD.Export.TPTP as TPTP

export :: SourcePos -> Int -> [Prover] -> [Instr] -> [Context] -> Context -> IO Result
export pos depth provers instrs context goal = do
  Isabelle_Thread.expose_stopped

  when (null provers) $ Message.errorExport pos "No provers"

  let proverName = Text.unpack $ askArgument Instr.Prover (Text.pack $ name $ head provers) instrs
      proversNamed = filter ((==) proverName . name) provers

  when (null proversNamed) $
    Message.errorExport pos ("No prover named " <> proverName)

  let printProver = askFlag Printprover False instrs
  let timeLimit = askLimit Timelimit 3 instrs
  let memoryLimit = askLimit Memorylimit 2048 instrs

  let proverServerPort = askArgument ProverServerPort Text.empty instrs
  let proverServerPassword =
        make_bytes $ Text.unpack $ askArgument ProverServerPassword Text.empty instrs
  let proverServer =
        if Text.null proverServerPort || Bytes.null proverServerPassword then
          Nothing
        else Just (Text.unpack proverServerPort, proverServerPassword)

  let task = TPTP.output context goal
  let isByContradiction = any (==Block.ProofByContradiction)
        (map Block.kind (head (branch goal) : concatMap branch context))

  when (askFlag Dump False instrs) $
    Message.output Bytes.empty Message.WRITELN pos task

  reportBracketIO pos $
    runProver pos (head proversNamed) proverServer printProver task isByContradiction timeLimit memoryLimit

data Result = Success | Failure | ContradictoryAxioms | Unknown | Error
  deriving (Eq, Ord, Show)

runProver :: SourcePos -> Prover -> Maybe (String, Bytes) -> Bool -> Text -> Bool -> Int -> Int -> IO Result
runProver pos (Prover _ label path args yes con nos uns) proverServer printProver task isByContradiction timeLimit memoryLimit =
  let
    proverResult :: Int -> String -> IO Result
    proverResult rc output =
      do
        let timeout = rc == 142
        let lns = filter notNull (lines output)
        let out = map (("[" ++ label ++ "] ") ++) lns

        when (not timeout && null lns) $ Message.errorExport pos "No prover response"
        when printProver $ mapM_ (Message.output Bytes.empty Message.WRITELN pos) out

        let contradictions = any (\l -> any (`isPrefixOf` l) con) lns
            positive = any (\l -> any (`isPrefixOf` l) yes) lns
            negative = any (\l -> any (`isPrefixOf` l) nos) lns
            inconclusive = any (\l -> any (`isPrefixOf` l) uns) lns

        unless (timeout || positive || contradictions || negative || inconclusive) $
            Message.errorExport pos $ unlines ("Bad prover response:" : lns)

        if | positive || (isByContradiction && contradictions) -> pure Success
           | negative -> pure Failure
           | not isByContradiction && contradictions -> pure ContradictoryAxioms
           | timeout -> pure Unknown
           | otherwise -> pure Error
  in
    case proverServer of
      Nothing -> do
        let proc = (Process.proc path (map (setLimits timeLimit memoryLimit) args))
              { Process.std_in = Process.CreatePipe
              ,  Process.std_out = Process.CreatePipe
              ,  Process.std_err = Process.CreatePipe
              ,  Process.create_group = True
              ,  Process.new_session = True}
        let process = do
              (pin, pout, perr, p) <- Process.createProcess proc
              return (fromJust pin, fromJust pout, fromJust perr, p)

        (prvin, prvout, prverr, prv) <- Exception.catch process
            (\e -> Message.errorExport pos $
              ("Failed to run " ++ show path ++ ": " ++ ioeGetErrorString e))

        UTF8.setup3 prvin prvout prverr

        TIO.hPutStrLn prvin task
        hClose prvin

        let terminate = do
              Process.interruptProcessGroupOf prv
              Process.waitForProcess prv
              return ()

        Isabelle_Thread.bracket_resource terminate $ do
          output <- ByteString.hGetContents prvout
          errors <- ByteString.hGetContents prverr
          exitCode <- Process.waitForProcess prv
          let rc =
                case exitCode of
                  ExitSuccess -> 0
                  ExitFailure rc | rc >= 0 -> rc
                  ExitFailure rc -> 128 - rc

          proverResult rc (make_string (Bytes.make (output <> errors)))

      Just (port, password) ->
        Server.connection port password
          (\prover ->
            do
              Byte_Message.write_yxml prover
                [XML.Elem ((Naproche.prover_command,
                    [(Naproche.prover_name, make_bytes path),
                     (Naproche.command_args, make_bytes $ unlines (map (setLimits 300 2048) args)),
                     (Naproche.prover_timeout, Value.print_int timeLimit)]),
                  [XML.Text (make_bytes task)])]

              reply <- Byte_Message.read_line_message prover

              case reply of
                Nothing -> proverResult 0 ""
                Just uuid ->
                  do
                    let kill_prover = do
                          Server.connection port password (\prover_kill ->
                            Byte_Message.write_yxml prover_kill
                              [XML.Elem ((Naproche.kill_command, []),
                                [XML.Text uuid])])
                    (rc, output) <-
                      Isabelle_Thread.bracket_resource kill_prover $ do
                        result <- Byte_Message.read_yxml prover
                        return $
                          case result of
                            Just [XML.Elem ((elem, (a, b) : _), body)] |
                              elem == Naproche.prover_result &&
                              a == Naproche.prover_return_code ->
                                case Value.parse_int b of
                                  Just rc -> (rc, XML.content_of body)
                                  Nothing -> (2, Bytes.empty)
                            _ -> (2, Bytes.empty)

                    proverResult rc (make_string output))


setLimits :: Int -> Int -> String -> String
setLimits timeLimit memoryLimit = go
  where
    go ('%':'t':rs) = show timeLimit ++ go rs
    go ('%':'m':rs) = show memoryLimit ++ go rs
    go (s:rs) = s : go rs
    go [] = []