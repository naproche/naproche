{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module CommandLine where

import Prelude hiding (error)
import Data.Maybe
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.UTF8 as UTF8
import qualified Isabelle.YXML as YXML
import qualified Isabelle.XML as XML
import qualified Isabelle.Markup as Markup
import SAD.Data.Message
import SAD.Data.SourcePos
import Control.Monad
import Control.Exception
import Control.Monad.IO.Class
import Control.Monad.State
import Data.Binary (Binary, decodeOrFail, encode)
import System.Directory
import System.FilePath
import System.IO
import System.IO.Error
import System.Exit (ExitCode(..))

import qualified Control.Exception as Exception
import qualified Data.ByteString.Lazy as BS
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import qualified System.Process as Process

import qualified Isabelle.File as File
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread

import SAD.Core.Cache (CacheStorage(..), FileCache(..))
import SAD.Core.Provers (Prover(..))
import SAD.Core.Prove (RunProver(..))
import SAD.Core.Reader (HasLibrary(..))
import SAD.Core.Unique

import PIDE
import TermSize (getTermSize)

data CommandLineConfig = CommandLineConfig
  { cacheDir :: FilePath
  , libraryDir :: FilePath
  } deriving (Eq, Ord, Show)

newtype CommandLine a = CommandLine
  { fromCommandLine :: StateT CommandLineConfig (UniqueT IO) a
  } deriving (Functor, Applicative, Monad, MonadIO, MonadState CommandLineConfig)

instance HasUnique CommandLine where
  newIdent = CommandLine . lift . newIdent

runCommandLine :: String -> CommandLine a -> IO a
runCommandLine libraryDir = fmap fst . runUnique . flip evalStateT (CommandLineConfig ".ftlcache" libraryDir) . fromCommandLine

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

  textFieldWidth = do
    w <- getTermSize
    pure $ case snd w of
      0 -> 120
      n -> n

instance Comm CommandLine where
  output o k p m = liftIO $ output o k p m
  error o p m = liftIO $ error o p m
  reportsString a = liftIO $ reportsString a
  pideContext = liftIO pideContext
  textFieldWidth = liftIO textFieldWidth

decode' :: Binary a => BS.ByteString -> Maybe a
decode' b = case decodeOrFail b of
  Right (_, _, a) -> Just a
  Left _ -> Nothing

instance CacheStorage CommandLine where
  readFileCache f = do
    let (fdir, fname) = splitFileName f
    dirname <- cacheDir <$> get
    let dir = fdir </> dirname
    liftIO $ createDirectoryIfMissing True dir
    c <- liftIO $ ((decode' . BS.fromStrict) <$> ByteString.readFile (dir </> fname))
      `catch` (\(_ :: SomeException) -> pure Nothing)
    case c of
      Just c' -> pure $ c' { lastRun = 1 + lastRun c' }
      Nothing -> pure $ mempty

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
  runProver pos (Prover _ path args _ yes con nos uns) timeLimit memoryLimit task =
    liftIO $ reportBracketIO pos $ do
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

setLimits :: Int -> Int -> String -> String
setLimits timeLimit memoryLimit = go
  where
    go ('%':'t':rs) = show timeLimit ++ go rs
    go ('%':'m':rs) = show memoryLimit ++ go rs
    go (s:rs) = s : go rs
    go [] = []
