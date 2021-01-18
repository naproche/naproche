{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Control.Exception
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.State
import Data.Binary (decode, encode)
import Data.Either (isRight)
import Data.Maybe
import Data.Time (UTCTime, NominalDiffTime, getCurrentTime, diffUTCTime)
import Network.Socket (Socket)
import System.Directory
import System.FilePath
import System.IO
import System.IO.Error

import qualified Control.Exception as Exception
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BS
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import qualified System.Console.GetOpt as GetOpt
import qualified System.Environment as Environment
import qualified System.Process as Process
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

import SAD.Core.Cache (CacheStorage(..), FileCache(..))
import SAD.Core.Message (Comm, errorParser, errorExport, outputMain, Kind(..))
import SAD.Core.Provers (readProverDatabase, Prover(..))
import SAD.Core.Prove (RunProver(..))
import SAD.Core.Reader (HasLibrary(..), parseInit)
import SAD.Core.SourcePos (noSourcePos, fileOnlyPos)
import SAD.Data.Instr (Instr(..), Flag(..), askFlag, Argument(..), askArgument, noPos, Pos, ParserKind)
import SAD.Data.Text.Block (ProofText(..))

import SAD.Main
import PIDE

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
  (opts0, pk, mFileName) <- readArgs' args0
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
          (opts0, pk, _) <- readArgs' (args0 ++ args1)
          let opts1 = map snd opts0
          let text0 = map (uncurry ProofTextInstr) (reverse opts0)
          let text1 = text0 ++ [ProofTextInstr noPos (GetArgument (Text pk) (Text.pack $ XML.content_of body))]

          Exception.catch (consoleMainBody opts1 text1)
            (\err -> do
              let msg = Exception.displayException (err :: Exception.SomeException)
              Exception.catch
                (if YXML.detect msg then
                  Byte_Message.write connection [UTF8.fromString msg]
                 else outputMain ERROR noSourcePos msg)
                (\(_ :: Exception.IOException) -> pure ())))

    _ -> return ()

consoleMainBody :: [Instr] -> [ProofText] -> IO ()
consoleMainBody opts0 text0 = do
  let proversFile = Text.unpack (askArgument Provers "provers.yaml" opts0)
  provers <- readProverDatabase proversFile =<< liftIO (B.readFile proversFile)
  let library = Text.unpack $ askArgument Library "." opts0
  exit <- withLibrary library $ runTimedIO (mainBody provers opts0 text0)
  Exit.exitWith exit

readArgs' :: (MonadIO m, Comm m) => [String] -> m ([(Pos, Instr)], ParserKind, Maybe FilePath)
readArgs' args = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args
  unless (null errs) $ errorWithoutStackTrace (unlines (map trim_line errs))

  let initFilePath = Text.unpack $ askArgument Init "init.opt" instrs
  initFileContent <- liftIO $ File.read initFilePath 
    `Exception.catch` (errorParser (fileOnlyPos initFilePath) . ioeGetErrorString)
  initFile <- liftIO $ parseInit initFilePath $ Text.pack initFileContent

  let initialOpts = initFile ++ map (noPos,) instrs
  readArgs initialOpts files


newtype Timed m a = Timed
  { fromTimed :: StateT (Map.Map TimedSection (Either UTCTime NominalDiffTime)) m a }
  deriving (Functor, Applicative, Monad, MonadIO
    , MonadState (Map.Map TimedSection (Either UTCTime NominalDiffTime))
    , RunProver, Comm, CacheStorage, HasLibrary)

runTimedIO :: MonadIO m => Timed m a -> m a
runTimedIO = fmap fst . flip runStateT mempty . fromTimed

instance MonadIO m => TimeStatistics (Timed m) where
  beginTimedSection t = do
    time <- liftIO $ getCurrentTime
    modify $ Map.insert t (Left time)
  endTimedSection t = do
    time <- liftIO $ getCurrentTime
    modify $ \m -> case Map.lookup t m of
      Just (Left begin) -> Map.insert t (Right $ diffUTCTime time begin) m
      _ -> m
  getTimes = takeRights <$> get
    where takeRights = Map.map (\(Right r) -> r) . Map.filter isRight

instance CacheStorage m => CacheStorage (StateT s m) where
  readFileCache f = lift $ readFileCache f
  writeFileCache f c = lift $ writeFileCache f c

instance CacheStorage m => CacheStorage (ReaderT s m) where
  readFileCache f = lift $ readFileCache f
  writeFileCache f c = lift $ writeFileCache f c

dirname :: FilePath
dirname = ".ftlcache"

instance CacheStorage IO where
  readFileCache f = do
    let (fdir, fname) = splitFileName f
    let dir = fdir </> dirname
    createDirectoryIfMissing True dir
    c <- (decode <$> BS.readFile (dir </> fname))
      `catch` (\(_ :: SomeException) -> pure mempty)
    pure $ c { lastRun = 1 + lastRun c }

  writeFileCache f c = do
    let (fdir, fname) = splitFileName f
    let dir = fdir </> dirname
    createDirectoryIfMissing True dir
    BS.writeFile (dir </> fname) (encode c)

newtype WithLibrary a = WithLibrary { fromWithLibrary :: ReaderT FilePath IO a }
  deriving (Functor, Applicative, Monad, MonadReader FilePath, MonadIO, Comm, RunProver, CacheStorage)

instance HasLibrary m => HasLibrary (StateT s m) where
  readLibrary = lift . readLibrary

instance HasLibrary WithLibrary where
  readLibrary f
    --- This an be used for protection against attacks:
    --- | ".." `isInfixOf` f = 
    ---   Message.errorParser (fileOnlyPos f) ("Illegal \"..\" in file name: " ++ show f)
    | otherwise = do
      library <- ask
      ex_f <- liftIO $ doesFileExist f
      ex_lf <- liftIO $ doesFileExist $ library </> f
      file <- case (ex_f, ex_lf) of
        (True, _) -> pure f
        (_, True) -> pure $ library </> f
        _ -> errorParser (fileOnlyPos f) $ "File not found! Neither " ++ f ++ " nor " ++ (library </> f)
          ++ " is a valid file path!"
      content <- liftIO $ fmap Text.pack $ catch (if null file then getContents else File.read file)
        (errorParser (fileOnlyPos file) . ioeGetErrorString)
      pure (file, content)

withLibrary :: FilePath -> WithLibrary a -> IO a
withLibrary f = flip runReaderT f . fromWithLibrary

setTimeLimit :: Int -> String -> String
setTimeLimit timeLimit ('%':'d':rs) = show timeLimit ++ rs
setTimeLimit timeLimit (s:rs) = s : setTimeLimit timeLimit rs
setTimeLimit _ _ = []

instance RunProver m => RunProver (StateT s m) where
  runProver a b c = lift $ runProver a b c
instance RunProver m => RunProver (ReaderT s m) where
  runProver a b c = lift $ runProver a b c

instance RunProver IO where
  runProver (Prover _ _ path args _ _ _ _) timeLimit task = do
    let proc = (Process.proc path (map (setTimeLimit timeLimit) args))
          { Process.std_in = Process.CreatePipe
          ,  Process.std_out = Process.CreatePipe
          ,  Process.std_err = Process.CreatePipe
          ,  Process.create_group = True
          ,  Process.new_session = True}
    let process = do
          (pin, pout, perr, p) <- Process.createProcess proc
          return (fromJust pin, fromJust pout, fromJust perr, p)

    Isabelle_Thread.expose_stopped
    (prvin, prvout, prverr, prv) <- Exception.catch process
        (\e -> errorExport noSourcePos $
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
      output <- TIO.hGetContents prvout
      errors <- TIO.hGetContents prverr
      hClose prverr
      Process.waitForProcess prv
      pure $ output <> errors