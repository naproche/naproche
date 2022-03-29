{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Control.Monad (when)
import Data.Maybe (mapMaybe)

import qualified Control.Exception as Exception
import Control.Exception (catch)
import qualified Data.Text.Lazy as Text
import qualified System.Console.GetOpt as GetOpt
import qualified System.Environment as Environment
import Network.Socket (Socket)

import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Naproche as Naproche
import qualified Isabelle.Server as Server
import qualified Isabelle.Options as Options
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread
import qualified Isabelle.UUID as UUID
import qualified Isabelle.Position as Position
import qualified Isabelle.YXML as YXML
import qualified Isabelle.Process_Result as Process_Result
import qualified Isabelle.File
import Isabelle.Library

import SAD.Data.Instr
import qualified SAD.Core.Message as Message
import SAD.API

import qualified Naproche.Program as Program
import qualified Naproche.Console as Console
import qualified Naproche.File as File

import qualified SAD.Main
import qualified PIDE
import System.IO.Error (ioeGetErrorString)

main :: IO ()
main  = do
  Console.setup

  -- command line and init file
  args0 <- Environment.getArgs
  (opts0, pk, fileArg) <- SAD.Main.readArgs args0
  text0 <- (map (uncurry ProofTextInstr) (reverse opts0) ++) <$> case fileArg of
    Nothing -> do
      stdin <- getContents
      pure [ProofTextInstr Position.none $ GetArgument (Text pk) (Text.pack stdin)]
    Just name -> do
      pure [ProofTextInstr Position.none $ GetArgument (File pk) (Text.pack name)]
  let opts1 = map snd opts0

  if getInstr helpParam opts1 then
    putStr (GetOpt.usageInfo SAD.Main.usageHeader SAD.Main.options)
  else -- main body with explicit error handling, notably for PIDE
      (if getInstr serverParam opts1 then
        Server.server (Server.publish_stdout "Naproche-SAD") (mainServer args0)
      else do
        Program.init_console
        rc <- do
          SAD.Main.mainBody opts1 text0 fileArg
            `catch` (\Exception.UserInterrupt -> do
              Program.exit_thread
              Console.stderr ("Interrupt" :: String)
              return Process_Result.interrupt_rc)
            `catch` (\(err :: Exception.SomeException) -> do
              Program.exit_thread
              Console.stderr (Exception.displayException err)
              return 1)
        Console.exit rc)

mainServer :: [String] -> Socket -> IO ()
mainServer args0 socket =
  let
    exchange_message0 = Byte_Message.exchange_message0 socket
    robust_error msg =
      exchange_message0 [Naproche.output_error_command, msg]
        `catch` (\(_ :: Exception.IOException) -> return ())
  in
    do
      chunks <- Byte_Message.read_message socket
      case chunks of
        Just (command : threads) | command == Naproche.cancel_program ->
          mapM_ Isabelle_Thread.stop_uuid (mapMaybe UUID.parse threads)

        Just [command, more_args, opts, text] | command == Naproche.forthel_program -> do
          let options = Options.decode $ YXML.parse_body opts

          Exception.bracket_ (PIDE.init_pide socket options)
            Program.exit_thread
            (do
              thread_uuid <- Isabelle_Thread.my_uuid
              mapM_ (\uuid -> exchange_message0 [Naproche.threads_command, UUID.print uuid]) thread_uuid

              let more_text = Text.pack $ make_string text

              (opts0, pk, fileArg) <- SAD.Main.readArgs (args0 ++ lines (make_string more_args))
              let opts1 = map snd opts0
              let text0 = map (uncurry ProofTextInstr) (reverse opts0)
              let text1 = text0 ++ [ProofTextInstr Position.none (GetArgument (Text pk) more_text)]

              rc <- do
                SAD.Main.mainBody opts1 text1 fileArg
                  `catch` (\(err :: Program.Error) -> do
                    robust_error $ Program.print_error err
                    return 0)
                  `catch` (\(err :: Exception.SomeException) -> do
                    robust_error $ make_bytes $ Exception.displayException err
                    return 0)

              when (rc /= 0) $ robust_error "ERROR")

        _ -> return ()

instance File.MonadFile IO where
  read f = catch (Isabelle.File.read f)
    (Message.errorParser (Position.file_only $ make_bytes f) . make_bytes . ioeGetErrorString)
  write f b = catch (Isabelle.File.write f b)
    (Message.errorParser (Position.file_only $ make_bytes f) . make_bytes . ioeGetErrorString)
  append f b = catch (Isabelle.File.append f b)
    (Message.errorParser (Position.file_only $ make_bytes f) . make_bytes . ioeGetErrorString)