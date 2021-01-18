{-# LANGUAGE OverloadedStrings #-}

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

import qualified Control.Exception as Exception
import qualified Data.ByteString.Lazy as BS
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified Data.Text.IO as TIO
import qualified System.Process as Process

import qualified Isabelle.File as File
import qualified Isabelle.Isabelle_Thread as Isabelle_Thread

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

instance Comm CommandLine where
  output origin kind pos msg = do
    context <- liftIO $ getContext
    liftIO $ channel context $ messageBytes (pide context) origin kind pos msg

  error origin pos msg = do
    pide <- pideContext
    errorWithoutStackTrace $
      UTF8.toString $ ByteString.concat $ messageBytes pide origin ERROR pos msg

  reportsString args = do
    context <- liftIO $ getContext
    when (isJust (pide context) && not (null args)) $
      liftIO $ channel context $ pideMessage $ YXML.string_of $
        XML.Elem (Markup.report,
          map (\((pos, markup), txt) ->
            let
              markup' = Markup.properties (posProperties (fromJust (pide context)) pos) markup
              body = if null txt then [] else [XML.Text txt]
            in XML.Elem (markup', body)) args)

  pideContext = pide <$> (liftIO getContext)

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

instance RunProver CommandLine where
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

    liftIO $ Isabelle_Thread.expose_stopped
    (prvin, prvout, prverr, prv) <- liftIO $ Exception.catch process
        (\e -> runCommandLine "" . errorExport noSourcePos $
          "Failed to run " ++ show path ++ ": " ++ ioeGetErrorString e)

    liftIO $ File.setup prvin
    liftIO $ File.setup prvout
    liftIO $ File.setup prverr

    liftIO $ TIO.hPutStrLn prvin task
    liftIO $ hClose prvin

    let terminate = do
          Process.interruptProcessGroupOf prv
          Process.waitForProcess prv
          return ()

    liftIO $ Isabelle_Thread.bracket_resource terminate $ do
      output <- TIO.hGetContents prvout
      errors <- TIO.hGetContents prverr
      hClose prverr
      Process.waitForProcess prv
      pure $ output <> errors

setTimeLimit :: Int -> String -> String
setTimeLimit timeLimit ('%':'d':rs) = show timeLimit ++ rs
setTimeLimit timeLimit (s:rs) = s : setTimeLimit timeLimit rs
setTimeLimit _ _ = []