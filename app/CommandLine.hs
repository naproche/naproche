{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module CommandLine where

import Prelude hiding (error)
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.UTF8 as UTF8
import qualified Isabelle.YXML as YXML
import qualified Isabelle.XML as XML
import qualified Isabelle.Markup as Markup
import SAD.Core.Message
import SAD.Core.SourcePos
import Control.Monad
import Control.Exception
import Control.Monad.IO.Class
import Control.Monad.State
import Data.Binary (decode, encode)
import Data.Either (isRight)
import Data.Time (UTCTime, NominalDiffTime, getCurrentTime, diffUTCTime)
import System.Directory
import System.FilePath
import System.IO
import System.IO.Error
import System.Exit (ExitCode(..))

import qualified Control.Exception as Exception
import qualified Data.ByteString.Lazy as BS
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import qualified System.Process as Process

import qualified Isabelle.File as File
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread
import qualified Isabelle.Server as Server
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Value as Value
import qualified Isabelle.Naproche as Naproche

import SAD.Core.Cache (CacheStorage(..), FileCache(..))
import SAD.Core.Provers (Prover(..))
import SAD.Core.Prove (RunProver(..))
import SAD.Core.Reader (HasLibrary(..))

import SAD.Main

import PIDE

data CommandLineConfig = CommandLineConfig
  { cacheDir :: FilePath
  , times :: Map TimedSection (Either UTCTime NominalDiffTime)
  , libraryDir :: FilePath
  } deriving (Eq, Ord, Show)

newtype CommandLine a = CommandLine
  { fromCommandLine :: StateT CommandLineConfig IO a
  } deriving (Functor, Applicative, Monad, MonadIO, MonadState CommandLineConfig)

runCommandLine :: String -> CommandLine a -> IO a
runCommandLine libraryDir = flip evalStateT (CommandLineConfig ".ftlcache" mempty libraryDir) . fromCommandLine

instance Comm IO where
  output origin kind pos msg = do
    context <- getContext
    channel context $ messageBytes (pide context) origin kind pos msg

  error origin pos msg = do
    pide <- pideContext
    errorWithoutStackTrace $
      UTF8.toString $ ByteString.concat $ messageBytes pide origin ERROR pos msg

  reportsString args = do
    context <- getContext
    when (isJust (pide context) && not (null args)) $
      channel context $ pideMessage $ YXML.string_of $
        XML.Elem (Markup.report,
          map (\((pos, markup), txt) ->
            let
              markup' = Markup.properties (posProperties (fromJust (pide context)) pos) markup
              body = if null txt then [] else [XML.Text txt]
            in XML.Elem (markup', body)) args)

  pideContext = pide <$> getContext 

instance Comm CommandLine where
  output o k p m = liftIO $ output o k p m
  error o p m = liftIO $ error o p m
  reportsString a = liftIO $ reportsString a
  pideContext = liftIO pideContext

instance TimeStatistics CommandLine where
  beginTimedSection t = do
    time <- liftIO $ getCurrentTime
    modify $ \c -> c { times = Map.insert t (Left time) (times c) }
  endTimedSection t = do
    time <- liftIO $ getCurrentTime
    modify $ \c -> case Map.lookup t (times c) of
      Just (Left begin) -> c { times = Map.insert t (Right $ diffUTCTime time begin) (times c) }
      _ -> c
  getTimes = (takeRights . times) <$> get
    where takeRights = Map.map (\(Right r) -> r) . Map.filter isRight

instance CacheStorage CommandLine where
  readFileCache f = do
    let (fdir, fname) = splitFileName f
    dirname <- cacheDir <$> get
    let dir = fdir </> dirname
    liftIO $ createDirectoryIfMissing True dir
    c <- liftIO $ (decode <$> BS.readFile (dir </> fname))
      `catch` (\(_ :: SomeException) -> pure mempty)
    pure $ c { lastRun = 1 + lastRun c }

  writeFileCache f c = do
    let (fdir, fname) = splitFileName f
    dirname <- cacheDir <$> get
    let dir = fdir </> dirname
    liftIO $ createDirectoryIfMissing True dir
    liftIO $ BS.writeFile (dir </> fname) (encode c)

instance HasLibrary CommandLine where
  readLibrary f
    --- This an be used for protection against attacks:
    --- | ".." `isInfixOf` f = 
    ---   Message.errorParser (fileOnlyPos f) ("Illegal \"..\" in file name: " ++ show f)
    | otherwise = do
      library <- libraryDir <$> get
      ex_f <- liftIO $ doesFileExist f
      ex_lf <- liftIO $ doesFileExist $ library </> f
      file <- case (ex_f, ex_lf) of
        (True, _) -> pure f
        (_, True) -> pure $ library </> f
        _ -> errorParser (fileOnlyPos f) $ "File not found! Neither " ++ f ++ " nor " ++ (library </> f)
          ++ " is a valid file path!"
      content <- liftIO $ fmap Text.pack $ catch (if null file then getContents else File.read file)
        (runCommandLine "" . errorParser (fileOnlyPos file) . ioeGetErrorString)
      pure (file, content)

-- Markup reports (with exception handling)
reportBracketIO :: SourcePos -> IO a -> IO a
reportBracketIO pos body = do
  report pos Markup.running
  (res :: Either Exception.SomeException a) <- try body
  case res of
    Left e -> do
      report pos Markup.failed
      report pos Markup.finished
      throw e
    Right x -> do
      report pos Markup.finished
      return x

instance RunProver CommandLine where
  runProver pos (Prover _ label path args yes con nos uns) proverServer timeLimit memoryLimit task =
    liftIO $ reportBracketIO pos $ case proverServer of
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
            (\e -> errorExport pos $
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
          exitCode <- Process.waitForProcess prv
          let rc =
                case exitCode of
                  ExitSuccess -> 0
                  ExitFailure rc | rc >= 0 -> rc
                  ExitFailure rc -> 128 - rc

          pure (rc, Text.pack $ UTF8.toString output ++ UTF8.toString errors)

      Just (port, password) ->
        Server.connection port password
          (\prover ->
            do
              Byte_Message.write_yxml prover
                [XML.Elem ((Naproche.prover_command,
                    [(Naproche.prover_name, path),
                    (Naproche.command_args, unlines (map (setLimits 300 2048) args)),
                    (Naproche.prover_timeout, show timeLimit)]),
                  [XML.Text (Text.unpack task)])]

              reply <- Byte_Message.read_line_message prover

              case reply of
                Nothing -> pure (0, "")
                Just uuid ->
                  do
                    let kill_prover = do
                          Server.connection port password (\prover_kill ->
                            Byte_Message.write_yxml prover_kill
                              [XML.Elem ((Naproche.kill_command, []),
                                [XML.Text (UTF8.toString uuid)])])
                    Isabelle_Thread.bracket_resource kill_prover $ do
                      result <- Byte_Message.read_yxml prover
                      return $
                        case result of
                          Just [XML.Elem ((elem, (a, b) : _), body)] |
                            elem == Naproche.prover_result &&
                            a == Naproche.prover_return_code ->
                              case Value.parse_int b of
                                Just rc -> (rc, Text.pack $ XML.content_of body)
                                Nothing -> (2, "")
                          _ -> (2, ""))


setLimits :: Int -> Int -> String -> String
setLimits timeLimit memoryLimit = go
  where
    go ('%':'t':rs) = show timeLimit ++ go rs
    go ('%':'m':rs) = show memoryLimit ++ go rs
    go (s:rs) = s : go rs
    go [] = []
