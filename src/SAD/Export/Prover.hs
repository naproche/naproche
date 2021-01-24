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
import qualified System.Process as Process
import qualified Control.Exception as Exception
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as TIO
import Data.Text.Lazy (Text)

import qualified Isabelle.File as File
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread
import qualified Isabelle.Server as Server
import qualified Isabelle.XML as XML
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Naproche as Naproche


import SAD.Core.SourcePos
import SAD.Data.Instr hiding (Prover)
import SAD.Data.Text.Context (Context, branch)
import qualified SAD.Data.Text.Block as Block
import SAD.Export.Base
import SAD.Helpers (notNull)

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Instr as Instr
import qualified SAD.Export.TPTP as TPTP

export :: Int -> [Prover] -> [Instr] -> [Context] -> Context -> IO Result
export depth provers instrs context goal = do
  Isabelle_Thread.expose_stopped

  when (null provers) $ Message.errorExport noSourcePos "No provers"

  let proverName = Text.unpack $ askArgument Instr.Prover (Text.pack $ name $ head provers) instrs
      proversNamed = filter ((==) proverName . name) provers

  when (null proversNamed) $
    Message.errorExport noSourcePos $ "No prover named " ++ show proverName

  let printProver = askFlag Printprover False instrs
  let timeLimit = askLimit Timelimit 3 instrs

  let proverServerPort = askArgument ProverServerPort Text.empty instrs
  let proverServerPassword = askArgument ProverServerPassword Text.empty instrs
  let proverServer =
        if Text.null proverServerPort || Text.null proverServerPassword then
          Nothing
        else Just (Text.unpack proverServerPort, Text.unpack proverServerPassword)

  let task = TPTP.output context goal
  let isByContradiction = any (==Block.ProofByContradiction)
        (map Block.kind (head (branch goal) : concatMap branch context))

  when (askFlag Dump False instrs) $
    Message.output "" Message.WRITELN noSourcePos (Text.unpack task)

  runUntilSuccess timeLimit $
    runProver (head proversNamed) proverServer printProver task isByContradiction

data Result = Success | Failure | TooLittleTime | ContradictoryAxioms
  deriving (Eq, Ord, Show)

-- | Prover heuristics are not always optimal.
-- We can give a different heuristic if needed.
runUntilSuccess :: Int -> (Int -> IO Result) -> IO Result
runUntilSuccess timeLimit f = go [timeLimit] -- go $ takeWhile (<=timeLimit) $ 1:5:10:20:50:(map (*100)[1,2])
  where
    go [] = pure TooLittleTime
    go (x:xs) = do
      b <- f x
      case b of
        TooLittleTime -> go xs
        r -> pure r

runProver :: Prover -> Maybe (String, String) -> Bool -> Text -> Bool -> Int -> IO Result
runProver (Prover _ label path args yes con nos uns) proverServer printProver task isByContradiction timeLimit =
  let
    proverResult output =
      do
        let lns = filter notNull (lines output)
        let out = map (("[" ++ label ++ "] ") ++) lns

        when (null lns) $ Message.errorExport noSourcePos "No prover response"
        when printProver $
            mapM_ (Message.output "" Message.WRITELN noSourcePos) out

        let contradictions = any (\l -> any (`isPrefixOf` l) con) lns
            positive = any (\l -> any (`isPrefixOf` l) yes) lns
            negative = any (\l -> any (`isPrefixOf` l) nos) lns
            inconclusive = any (\l -> any (`isPrefixOf` l) uns) lns

        unless (positive || contradictions || negative || inconclusive) $
            Message.errorExport noSourcePos $ unlines ("Bad prover response:" : lns)

        if | positive || (isByContradiction && contradictions) -> pure Success
           | negative -> pure Failure
           | not isByContradiction && contradictions -> pure ContradictoryAxioms
           | otherwise -> pure TooLittleTime
  in
    case proverServer of
      Nothing -> do
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

        Isabelle_Thread.bracket_resource terminate $ do
          output <- ByteString.hGetContents prvout
          errors <- ByteString.hGetContents prverr
          Process.waitForProcess prv

          proverResult (UTF8.toString output ++ UTF8.toString errors)

      Just (port, password) ->
        Server.connection port password
          (\prover ->
            do
              Byte_Message.write_yxml prover
                [XML.Elem ((Naproche.prover_command,
                    [(Naproche.prover_name, path),
                     (Naproche.command_args, unlines (map (setTimeLimit 300) args)),
                     (Naproche.prover_timeout, show timeLimit)]),
                  [XML.Text (Text.unpack task)])]

              reply <- Byte_Message.read_line_message prover

              case reply of
                Nothing -> proverResult ""
                Just uuid ->
                  do
                    let kill_prover = do
                          Server.connection port password (\prover_kill ->
                            Byte_Message.write_yxml prover_kill
                              [XML.Elem ((Naproche.kill_command, []),
                                [XML.Text (UTF8.toString uuid)])])
                    output <-
                      Isabelle_Thread.bracket_resource kill_prover $ do
                        result <- Byte_Message.read_yxml prover
                        return $
                          case result of
                            Just [XML.Elem ((elem, _), body)] | elem == Naproche.prover_result ->
                              XML.content_of body
                            _ -> ""

                    proverResult output)


setTimeLimit :: Int -> String -> String
setTimeLimit timeLimit ('%':'d':rs) = show timeLimit ++ rs
setTimeLimit timeLimit (s:rs) = s : setTimeLimit timeLimit rs
setTimeLimit _ _ = []