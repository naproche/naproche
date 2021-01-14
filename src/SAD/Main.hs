{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Main application entry point: console or server mode.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Main where

import Data.Maybe (fromMaybe)
import Data.Time (UTCTime, NominalDiffTime, getCurrentTime, diffUTCTime)
import qualified Data.ByteString as B
import Data.List (isSuffixOf)
import Data.Either (isRight)

import qualified Control.Exception as Exception
import qualified Data.Text as Text
import qualified System.Console.GetOpt as GetOpt
import qualified System.Environment as Environment
import qualified System.Exit as Exit
import qualified System.IO as IO
import qualified Data.Map as Map
import Control.Monad.State

import Isabelle.Library (trim_line)
import qualified Data.ByteString.UTF8 as UTF8
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.File as File
import qualified Isabelle.Naproche as Naproche
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Server as Server
import qualified Isabelle.Standard_Thread as Standard_Thread
import qualified Isabelle.UUID as UUID
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML
import Network.Socket (Socket)

import SAD.Core.Pretty (pretty)
import SAD.Core.Logging (showTimeDiff, RState(..), sumCounter, Counter(..))
import SAD.Core.Message (Comm, consoleThread, exitThread, errorParser, outputMain, initThread, Kind(..))
import SAD.Core.Provers (readProverDatabase)
import SAD.Core.Prove (RunProver(..), verify)
import SAD.Core.Reader (readInit, readProofText)
import SAD.Core.SourcePos (noSourcePos)
import SAD.Data.Text.Block (ProofText(..), findParseError)
import SAD.Data.Instr (Instr(..), Flag(..), askFlag, Limit(..), Argument(..), askArgument, noPos
  , ParserKind(..), Pos)
import SAD.Parser.Error (errorPos)
import SAD.Core.Transform (convert)
import SAD.Core.Typed (located)
import SAD.Core.Cache (CacheStorage)

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
  (opts0, pk, mFileName) <- readArgs args0
  text0 <- (map (uncurry ProofTextInstr) (reverse opts0) ++) <$> case mFileName of
    Nothing -> do
      stdin <- getContents
      pure $ [ProofTextInstr noPos $ GetArgument (Text pk) (Text.pack stdin)]
    Just f -> do
      pure $ [ProofTextInstr noPos $ GetArgument (File pk) (Text.pack f)]
  let opts1 = map snd opts0

  if askFlag Help False opts1 then
    putStr (GetOpt.usageInfo usageHeader options)
  else -- main body with explicit error handling, notably for PIDE
    Exception.catch
      (if askFlag Server False opts1 then
        Server.server (Server.publish_stdout "Naproche-SAD") (serverConnection args0)
      else do consoleThread; Exit.exitWith =<< runTimedIO (mainBody opts1 text0))
      (\err -> do
        exitThread
        let msg = Exception.displayException (err :: Exception.SomeException)
        IO.hPutStrLn IO.stderr msg
        Exit.exitFailure)

serverConnection :: [String] -> Socket -> IO ()
serverConnection args0 connection = do
  thread_uuid <- Standard_Thread.my_uuid
  mapM_ (Byte_Message.write_line_message connection . UUID.bytes) thread_uuid

  res <- Byte_Message.read_line_message connection
  case fmap (YXML.parse . UTF8.toString) res of
    Just (XML.Elem ((command, _), body)) | command == Naproche.cancel_command ->
      mapM_ Standard_Thread.stop_uuid (UUID.parse_string (XML.content_of body))

    Just (XML.Elem ((command, props), body)) | command == Naproche.forthel_command ->
      Exception.bracket_ (initThread props (Byte_Message.write connection))
        exitThread
        (do
          let args1 = lines (fromMaybe "" (Properties.get props Naproche.command_args))
          (opts0, pk, _) <- readArgs (args0 ++ args1)
          let opts1 = map snd opts0
          let text0 = map (uncurry ProofTextInstr) (reverse opts0)
          let text1 = text0 ++ [ProofTextInstr noPos (GetArgument (Text pk) (Text.pack $ XML.content_of body))]

          Exception.catch (Exit.exitWith =<< runTimedIO (mainBody opts1 text1))
            (\err -> do
              let msg = Exception.displayException (err :: Exception.SomeException)
              Exception.catch
                (if YXML.detect msg then
                  Byte_Message.write connection [UTF8.fromString msg]
                 else outputMain ERROR noSourcePos msg)
                (\(_ :: Exception.IOException) -> pure ())))

    _ -> return ()

data TimedSection = ParsingTime | ProvingTime
  deriving (Eq, Ord, Show)

class Monad m => TimeStatistics m where
  beginTimedSection :: TimedSection -> m ()
  endTimedSection :: TimedSection -> m ()
  getTimes :: m (Map.Map TimedSection NominalDiffTime)

newtype TimedIO a = TimedIO 
  { fromTimedIO :: StateT (Map.Map TimedSection (Either UTCTime NominalDiffTime)) IO a }
  deriving (Functor, Applicative, Monad, MonadIO
    , MonadState (Map.Map TimedSection (Either UTCTime NominalDiffTime))
    , RunProver, Comm, CacheStorage)

runTimedIO :: TimedIO a -> IO a
runTimedIO = fmap fst . flip runStateT mempty . fromTimedIO

instance TimeStatistics TimedIO where
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


mainBody :: (TimeStatistics m, RunProver m, Comm m, CacheStorage m, MonadIO m)
  => [Instr] -> [ProofText] -> m Exit.ExitCode
mainBody opts0 text0 = do

  beginTimedSection ParsingTime
  -- parse input text
  txts <- liftIO $ readProofText (askArgument Library "." opts0) text0

  -- if -T / --onlytranslate is passed as an option, only print the translated text
  if askFlag OnlyTranslate False opts0
    then showTranslation txts
    else do proveFOL txts opts0

showTranslation :: (TimeStatistics m, RunProver m, Comm m, CacheStorage m, MonadIO m)
  => [ProofText] -> m Exit.ExitCode
showTranslation txts = do
  -- mapM_ (\case (ProofTextBlock b) -> print b; _ -> pure ()) txts
  mapM_ (liftIO . putStr . (++"\n\n") . Text.unpack . pretty . located) (convert txts)

  -- print statistics
  endTimedSection ParsingTime
  times <- getTimes
  outputMain TRACING noSourcePos $ Text.unpack $ "total " <> showTimeDiff (times Map.! ParsingTime)
  pure $ Exit.ExitSuccess

proveFOL :: (TimeStatistics m, RunProver m, Comm m, CacheStorage m, MonadIO m) 
  => [ProofText] -> [Instr] -> m Exit.ExitCode
proveFOL txts opts0 = do
  -- read provers.yaml
  let proversFile = Text.unpack (askArgument Provers "provers.yaml" opts0)
  provers <- readProverDatabase proversFile =<< liftIO (B.readFile proversFile)

  case findParseError $ ProofTextRoot txts of
    Just err -> do 
      errorParser (errorPos err) (show err)
      pure $ Exit.ExitFailure 1
    Nothing -> do
      endTimedSection ParsingTime 
      beginTimedSection ProvingTime
      let typed = convert txts
      finalReasonerState <- verify provers opts0 (RState [] False False) typed
      endTimedSection ProvingTime

      let trackerList = trackers finalReasonerState
      let accumulate  = sumCounter trackerList

      -- print statistics
      outputMain TRACING noSourcePos $
        "sections "       ++ show (accumulate Sections)
        ++ " - goals "    ++ show (accumulate Goals)
        ++ (let ignoredFails = accumulate FailedGoals
            in  if   ignoredFails == 0
                then ""
                else " - failed "   ++ show ignoredFails)
        ++ " - proved "    ++ show (accumulate SuccessfulGoals)
        ++ " - cached "    ++ show (accumulate CachedCounter)

      times <- getTimes
      outputMain TRACING noSourcePos $ Text.unpack $
        "parser "           <> showTimeDiff (times Map.! ParsingTime)
        <> " - prover "     <> showTimeDiff (times Map.! ProvingTime)

      outputMain TRACING noSourcePos $ Text.unpack $
        "total " <> showTimeDiff ((times Map.! ParsingTime) + (times Map.! ProvingTime))

      pure $ if accumulate FailedGoals == 0 then Exit.ExitSuccess else Exit.ExitFailure 1

-- Command line parsing

readArgs :: MonadIO m => [String] -> m ([(Pos, Instr)], ParserKind, Maybe FilePath)
readArgs args = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args

  initFile <- liftIO $ readInit (Text.unpack $ askArgument Init "init.opt" instrs)
  let fail msgs = errorWithoutStackTrace (unlines (map trim_line msgs))
  unless (null errs) $ fail errs

  let initialOpts = initFile ++ map (noPos,) instrs

  let revInitialOpts = reverse initialOpts
  let useTexArg = askFlag UseTex False $ map snd revInitialOpts
  let fileName = case files of
                  [file] -> Just file
                  [] -> Nothing
                  _ -> fail ["More than one file argument\n"]
  let parserKind = if useTexArg || maybe False (".tex.ftl" `isSuffixOf`) fileName then Tex else NonTex
  pure (revInitialOpts, parserKind, fileName)

usageHeader :: String
usageHeader =
  "\nUsage: Naproche-SAD <options...> <file...>\n\n  At most one file argument may be given; \"\" refers to stdin.\n\n  Options are:\n"

options :: [GetOpt.OptDescr Instr]
options = [
  GetOpt.Option "h" ["help"] (GetOpt.NoArg (SetFlag Help True)) "show command-line help",
  GetOpt.Option ""  ["init"] (GetOpt.ReqArg (GetArgument Init . Text.pack) "FILE")
    "init file, empty to skip (def: init.opt)",
  GetOpt.Option "T" ["onlytranslate"] (GetOpt.NoArg (SetFlag OnlyTranslate True))
    "translate input text and exit",
  GetOpt.Option "" ["translate"] (GetOpt.ReqArg (SetFlag Translation . parseConsent) "{on|off}")
    "print first-order translation of sentences",
  GetOpt.Option "" ["server"] (GetOpt.NoArg (SetFlag Server True))
    "run in server mode",
  GetOpt.Option ""  ["library"] (GetOpt.ReqArg (GetArgument Library . Text.pack) "DIR")
    "place to look for library texts (def: .)",
  GetOpt.Option ""  ["provers"] (GetOpt.ReqArg (GetArgument Provers . Text.pack) "FILE")
    "index of provers (def: provers.yaml)",
  GetOpt.Option "P" ["prover"] (GetOpt.ReqArg (GetArgument Prover . Text.pack) "NAME")
    "use prover NAME (def: first listed)",
  GetOpt.Option "t" ["timelimit"] (GetOpt.ReqArg (LimitBy Timelimit . getLeadingPositiveInt) "N")
    "N seconds per prover call (def: 3)",
  GetOpt.Option ""  ["depthlimit"] (GetOpt.ReqArg (LimitBy Depthlimit . getLeadingPositiveInt) "N")
    "N reasoner loops per goal (def: 7)",
  GetOpt.Option ""  ["checktime"] (GetOpt.ReqArg (LimitBy Checktime . getLeadingPositiveInt) "N")
    "timelimit for checker's tasks (def: 1)",
  GetOpt.Option ""  ["checkdepth"] (GetOpt.ReqArg (LimitBy Checkdepth . getLeadingPositiveInt) "N")
    "depthlimit for checker's tasks (def: 3)",
  GetOpt.Option "n" [] (GetOpt.NoArg (SetFlag Prove False))
    "cursory mode (equivalent to --prove off)",
  GetOpt.Option "r" [] (GetOpt.NoArg (SetFlag Check False))
    "raw mode (equivalent to --check off)",
  GetOpt.Option "" ["prove"] (GetOpt.ReqArg (SetFlag Prove . parseConsent) "{on|off}")
    "prove goals in the text (def: on)",
  GetOpt.Option "" ["check"] (GetOpt.ReqArg (SetFlag Check . parseConsent) "{on|off}")
    "check symbols for definedness (def: on)",
  GetOpt.Option "" ["filter"] (GetOpt.ReqArg (SetFlag Filter . parseConsent) "{on|off}")
    "filter prover tasks (def: on)",
  GetOpt.Option "" ["skipfail"] (GetOpt.ReqArg (SetFlag Skipfail . parseConsent) "{on|off}")
    "ignore failed goals (def: off)",
  GetOpt.Option "q" [] (GetOpt.NoArg (SetFlag Verbose False))
    "print no details",
  GetOpt.Option "v" [] (GetOpt.NoArg (SetFlag Verbose True))
    "print more details (-vv, -vvv, etc)",
  GetOpt.Option "" ["printgoal"] (GetOpt.ReqArg (SetFlag Printgoal . parseConsent) "{on|off}")
    "print current goal (def: on)",
  GetOpt.Option "" ["printsection"] (GetOpt.ReqArg (SetFlag Printsection . parseConsent) "{on|off}")
    "print sentence translations (def: off)",
  GetOpt.Option "" ["printcheck"] (GetOpt.ReqArg (SetFlag Printcheck . parseConsent) "{on|off}")
    "print checker's messages (def: off)",
  GetOpt.Option "" ["printprover"] (GetOpt.ReqArg (SetFlag Printprover . parseConsent) "{on|off}")
    "print prover's messages (def: off)",
  GetOpt.Option "" ["printfulltask"] (GetOpt.ReqArg (SetFlag Printfulltask . parseConsent) "{on|off}")
    "print full prover tasks (def: off)",
  GetOpt.Option "" ["printsimp"] (GetOpt.ReqArg (SetFlag Printsimp . parseConsent) "{on|off}")
    "print simplification process (def: off)",
  GetOpt.Option "" ["printthesis"] (GetOpt.ReqArg (SetFlag Printthesis . parseConsent) "{on|off}")
    "print thesis development (def: off)",
  GetOpt.Option "" ["dump"]
    (GetOpt.ReqArg (SetFlag Dump . parseConsent) "{on|off}")
    "print tasks in prover's syntax (def: off)",
  GetOpt.Option "" ["tex"]
    (GetOpt.ReqArg (SetFlag UseTex . parseConsent) "{on|off}")
    "parse passed file with forthel tex parser (def: off)"
  ]

parseConsent :: String -> Bool
parseConsent "yes" = True ; parseConsent "on"  = True
parseConsent "no"  = False; parseConsent "off" = False
parseConsent s     = errorWithoutStackTrace $ "Invalid boolean argument: \"" ++ s ++ "\""

getLeadingPositiveInt :: String -> Int
getLeadingPositiveInt s = case reads s of
  ((n, []) : _) | n >= 0 -> n
  _ -> errorWithoutStackTrace $ "Invalid integer argument: \"" ++ s ++ "\""
