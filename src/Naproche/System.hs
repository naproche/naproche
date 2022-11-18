-- |
-- Authors: Makarius Wenzel (2021)
--
-- System process support for Naproche: with and without Isabelle/PIDE.


{-# LANGUAGE OverloadedStrings #-}

module Naproche.System (
  is_windows, bash_process
) where

import Data.Maybe (fromJust)
import System.IO qualified as IO
import System.IO.Temp qualified as Temp
import System.Process qualified as Process
import System.Exit qualified as Exit
import Control.Exception qualified as Exception
import Control.Exception (catch)
import Control.Monad (when)
import Data.ByteString qualified as ByteString
import System.Info qualified as Info

import Isabelle.Bash qualified as Bash
import Isabelle.Bytes qualified as Bytes
import Isabelle.Timing qualified as Timing
import Isabelle.Isabelle_Thread qualified as Isabelle_Thread
import Isabelle.Isabelle_System qualified as Isabelle_System
import Isabelle.Process_Result qualified as Process_Result
import Isabelle.UTF8 qualified as UTF8
import Isabelle.Library

import Naproche.Program qualified as Program


is_windows :: Bool
is_windows = Info.os == "mingw32"


bash_process :: Program.Context -> Bash.Params -> IO Process_Result.T
bash_process context params = do
  Isabelle_Thread.expose_stopped

  case Program.get_options context of
    Just options -> Isabelle_System.bash_process options params
    Nothing ->
      do
        when is_windows $ error "Windows OS: cannot run bash process from console"
        Temp.withSystemTempFile "script" (\tmp_name tmp_handle -> do
          let env =
                Bash.get_putenv params
                |> map (\(a, b) -> "export " <> Bash.string (a <> "=" <> b) <> "\n")
                |> Bytes.concat

          let script =
                if Bash.get_redirect params then
                  "eval " <> Bash.string (Bash.get_script params) <> " 2>&1"
                else Bash.get_script params

          ByteString.hPut tmp_handle (Bytes.unmake $ env <> script)
          IO.hClose tmp_handle

          let create_proc =
                (Process.proc "bash" [tmp_name])
                  {Process.std_in = Process.CreatePipe,
                    Process.std_out = Process.CreatePipe,
                    Process.std_err = Process.CreatePipe,
                    Process.delegate_ctlc = True,
                    Process.create_group = True,
                    Process.new_session = True,
                    Process.cwd = make_string <$> Bash.get_cwd params}

          let process = do
                (stdin, stdout, stderr, ph) <- Process.createProcess create_proc
                return (fromJust stdin, fromJust stdout, fromJust stderr, ph)

          (stdin, stdout, stderr, ph) <-
            process `catch` (\(exn :: Exception.IOException) ->
              error ("Failed to run bash process: " <> Exception.displayException exn))

          UTF8.setup3 stdin stdout stderr

          ByteString.hPut stdin (Bytes.unmake $ Bash.get_input params)
          IO.hClose stdin

          let terminate = do
                Process.interruptProcessGroupOf ph
                Process.waitForProcess ph
                return ()

          let make_lines = trim_split_lines . Bytes.make
          Isabelle_Thread.bracket_resource terminate $ do
            out_lines <- make_lines <$> ByteString.hGetContents stdout
            err_lines <- make_lines <$> ByteString.hGetContents stderr
            exit_code <- Process.waitForProcess ph
            let rc =
                  case exit_code of
                    Exit.ExitSuccess -> Process_Result.ok_rc
                    Exit.ExitFailure rc | rc >= 0 -> rc
                    Exit.ExitFailure rc -> 128 - rc
            return $ Process_Result.make rc out_lines err_lines Timing.zero)
