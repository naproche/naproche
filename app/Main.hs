{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Control.Monad.IO.Class
import Control.Monad.Reader
import Data.Maybe
import Network.Socket (Socket)
import System.IO.Error

import qualified Control.Exception as Exception
import qualified Data.ByteString as B
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.Text as Text
import qualified System.Console.GetOpt as GetOpt
import qualified System.Environment as Environment
import qualified System.Exit as Exit
import qualified System.IO as IO

import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.File as File
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread
import qualified Isabelle.Naproche as Naproche
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Server as Server
import qualified Isabelle.UUID as UUID
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML
import Isabelle.Library (trim_line)

import SAD.Core.Message (Comm, errorParser, outputMain, Kind(..))
import SAD.Core.Provers (readProverDatabase)
import SAD.Core.Reader (parseInit)
import SAD.Core.SourcePos (noSourcePos, fileOnlyPos)
import SAD.Data.Instr (Instr(..), Flag(..), askFlag, Argument(..), askArgument, noPos, Pos, ParserKind)
import SAD.Data.Text.Block (ProofText(..))

import SAD.Main
import PIDE (consoleThread, exitThread, initThread)
import CommandLine

main :: IO ()
main  = do
  -- setup stdin/stdout
  File.setup IO.stdin
  File.setup IO.stdout
  File.setup IO.stderr
  IO.hSetBuffering IO.stdout IO.LineBuffering
  IO.hSetBuffering IO.stderr IO.LineBuffering

  -- command line and init file
  args0 <- Environment.getArgs
  (opts0, pk, mFileName) <- runCommandLine "" $ readArgs' args0
  text0 <- (map (uncurry ProofTextInstr) (reverse opts0) ++) <$> case mFileName of
    Nothing -> do
      stdin <- getContents
      pure $ [ProofTextInstr noPos $ GetArgument (Text pk) (Text.pack stdin)]
    Just f -> do
      pure $ [ProofTextInstr noPos $ GetArgument (Read pk) (Text.pack f)]
  let opts1 = map snd opts0

  if askFlag Help False opts1 then
    putStr (GetOpt.usageInfo usageHeader options)
  else -- main body with explicit error handling, notably for PIDE
    Exception.catch
      (if askFlag Server False opts1 then
        Server.server (Server.publish_stdout "Naproche-SAD") (serverConnection args0)
      else do consoleThread; consoleMainBody opts1 text0)
      (\err -> do
        exitThread
        let msg = Exception.displayException (err :: Exception.SomeException)
        IO.hPutStrLn IO.stderr msg
        Exit.exitFailure)

serverConnection :: [String] -> Socket -> IO ()
serverConnection args0 connection = do
  thread_uuid <- Isabelle_Thread.my_uuid
  mapM_ (Byte_Message.write_line_message connection . UUID.bytes) thread_uuid

  res <- Byte_Message.read_line_message connection
  case fmap (YXML.parse . UTF8.toString) res of
    Just (XML.Elem ((command, _), body)) | command == Naproche.cancel_command ->
      mapM_ Isabelle_Thread.stop_uuid (UUID.parse_string (XML.content_of body))

    Just (XML.Elem ((command, props), body)) | command == Naproche.forthel_command ->
      Exception.bracket_ (initThread props (Byte_Message.write connection))
        exitThread
        (do
          let args1 = lines (fromMaybe "" (Properties.get props Naproche.command_args))
          (opts0, pk, _) <- runCommandLine "" $ readArgs' (args0 ++ args1)
          let opts1 = map snd opts0
          let text0 = map (uncurry ProofTextInstr) (reverse opts0)
          let text1 = text0 ++ [ProofTextInstr noPos (GetArgument (Text pk) (Text.pack $ XML.content_of body))]

          Exception.catch (consoleMainBody opts1 text1)
            (\err -> do
              let msg = Exception.displayException (err :: Exception.SomeException)
              Exception.catch
                (if YXML.detect msg then
                  Byte_Message.write connection [UTF8.fromString msg]
                 else runCommandLine "" $ outputMain ERROR noSourcePos msg)
                (\(_ :: Exception.IOException) -> pure ())))

    _ -> return ()

readArgs' :: (MonadIO m, Comm m) => [String] -> m ([(Pos, Instr)], ParserKind, Maybe FilePath)
readArgs' args = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args
  unless (null errs) $ errorWithoutStackTrace (unlines (map trim_line errs))

  let initFilePath = Text.unpack $ askArgument Init "init.opt" instrs
  initFileContent <- liftIO $ File.read initFilePath 
    `Exception.catch` (runCommandLine "" . errorParser (fileOnlyPos initFilePath) . ioeGetErrorString)
  initFile <- parseInit initFilePath $ Text.pack initFileContent

  let initialOpts = initFile ++ map (noPos,) instrs
  readArgs initialOpts files

consoleMainBody :: [Instr] -> [ProofText] -> IO ()
consoleMainBody opts0 text0 = do
  let library = Text.unpack $ askArgument Library "." opts0
  let proversFile = Text.unpack (askArgument Provers "provers.yaml" opts0)
  exit <- runCommandLine library $ do
    provers <- readProverDatabase proversFile =<< liftIO (B.readFile proversFile)
    mainBody provers opts0 text0
  Exit.exitWith exit