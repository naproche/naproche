{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018),
  Anton Lorenzen (2019 - 2021)

Main application entry point: console or server mode.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Main where

import Data.List (isSuffixOf)

import Data.Text (Text)
import qualified Data.Text as Text
import qualified System.Console.GetOpt as GetOpt
import qualified System.Exit as Exit
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Data.Either (isRight)
import Data.Time (NominalDiffTime, UTCTime, getCurrentTime, diffUTCTime)
import Data.Maybe (isNothing)

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import SAD.Core.Message (Comm, errorParser, outputMain, Kind(..), textFieldWidth, errorMain)
import SAD.Core.Provers (Prover)
import SAD.Core.Prove (RunProver(..), verify, runProveT, ProveState(..))
import SAD.Core.Reader (readProofText, HasLibrary(..))
import SAD.Core.SourcePos (SourcePos, noSourcePos, fileOnlyPos)
import SAD.Data.Text.Block (ProofText(..), findParseError)
import SAD.Data.Instr (Instr(..), Flag(..), askFlag, Limit(..), Argument(..), ParserKind(..), Pos)
import SAD.Parser.Error (errorPos)
import SAD.Core.Transform (transform)
import SAD.Core.Typed (located)
import SAD.Core.Cache (CacheStorage)
import SAD.Core.Task (Task(..))
import SAD.Core.Tactic (proofTasks, ontologicalTasks)
import SAD.Core.Typecheck (typecheck)

data TimedSection = ParsingTime | CheckTime | OntoTime | ProvingTime 
  deriving (Eq, Ord, Show)

newtype Times m a = Times { runTimes :: StateT (Map TimedSection (Either UTCTime NominalDiffTime)) m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadState (Map TimedSection (Either UTCTime NominalDiffTime)))

beginTimedSection :: MonadIO m => TimedSection -> Times m ()
beginTimedSection t = do
  time <- liftIO $ getCurrentTime
  modify $ Map.insert t (Left time)

endTimedSection :: MonadIO m => TimedSection -> Times m ()
endTimedSection t = do
  time <- liftIO $ getCurrentTime
  times <- get
  case Map.lookup t times of
    Just (Left begin) -> modify $ Map.insert t (Right $ diffUTCTime time begin)
    _ -> pure ()

getTimes :: MonadIO m => Times m (Map TimedSection NominalDiffTime)
getTimes = takeRights <$> get
  where takeRights = Map.map (\(Right r) -> r) . Map.filter isRight

mainBody :: (MonadIO m, RunProver m, Comm m, CacheStorage m, HasLibrary m)
  => [Prover] -> [Instr] -> [ProofText] -> m Exit.ExitCode
mainBody provers opts0 text0 = flip evalStateT mempty $ runTimes $ do
  beginTimedSection ParsingTime
  -- parse input text
  txts <- lift $ readProofText text0
  case findParseError $ ProofTextRoot txts of
    Just err -> do 
      lift $ errorParser (errorPos err) (show err)
      pure $ Exit.ExitFailure 1
    Nothing -> do
      endTimedSection ParsingTime
      -- if -T / --onlytranslate is passed as an option, only print the translated text
      if askFlag OnlyTranslate False opts0
        then showTranslation provers txts opts0
        else do proveFOL provers txts opts0

showTimeDiff :: NominalDiffTime -> Text
showTimeDiff t =
  if hours == 0
    then format minutes <> ":" <> format restSeconds <> "." <> format restCentis
    else format hours   <> ":" <> format restMinutes <> ":" <> format restSeconds
  where
    format n = Text.pack $ if n < 10 then '0':show n else show n
    centiseconds = (truncate $ t * 100) :: Int
    (seconds, restCentis)  = divMod centiseconds 100
    (minutes, restSeconds) = divMod seconds 60
    (hours,   restMinutes) = divMod minutes 60

showTimes :: (Comm m) => Map TimedSection NominalDiffTime -> m ()
showTimes times = do
  outputMain TRACING noSourcePos $ Text.unpack $
    "parser "           <> showTimeDiff (times Map.! ParsingTime)
    <> " - checker "     <> showTimeDiff (times Map.! CheckTime)
    <> " - ontological "     <> showTimeDiff (times Map.! OntoTime)
    <> " - prover "     <> showTimeDiff (times Map.! ProvingTime)

  outputMain TRACING noSourcePos $ Text.unpack $
    "total " <> showTimeDiff ((times Map.! ParsingTime) + (times Map.! CheckTime) + (times Map.! ProvingTime))

writeOut :: (Comm m) => SourcePos -> Doc ann -> m ()
writeOut pos doc = do
  w <- textFieldWidth
  outputMain WRITELN pos $ renderString $ layoutSmart
    (defaultLayoutOptions { layoutPageWidth = AvailablePerLine w 1.0 }) 
    (doc <> hardline)

showTranslation :: (MonadIO m, RunProver m, Comm m, CacheStorage m)
  => [Prover] -> [ProofText] -> [Instr] -> Times m Exit.ExitCode
showTranslation provers txts opts0 = do
  -- lift $ mapM_ (\case (ProofTextBlock b) -> outputMain WRITELN (fileOnlyPos "") $ show b; _ -> pure ()) txts
  
  beginTimedSection CheckTime
  converted <- lift $ transform txts
  -- lift $ mapM_ (writeOut (fileOnlyPos "") . pretty . located) converted
  typed <- lift $ typecheck converted
  endTimedSection CheckTime
  
  beginTimedSection OntoTime
  lift $ writeOut noSourcePos $ "Ontological checking:"
  proveTasks provers (ontologicalTasks typed) opts0
  endTimedSection OntoTime
  
  lift $ mapM_ (writeOut (fileOnlyPos "") . pretty . located) typed
  
  -- print statistics
  beginTimedSection ProvingTime
  endTimedSection ProvingTime
  getTimes >>= lift . showTimes
  pure $ Exit.ExitSuccess

proveTasks :: (MonadIO m, RunProver m, Comm m, CacheStorage m) 
  => [Prover] -> [Task] -> [Instr] -> Times m ProveState
proveTasks provers tasks opts0 = do
  proveOut <- lift $ fmap snd $ runProveT provers opts0 $ verify tasks
  if length (proveGoalsTimeout proveOut) == 0 then pure ()
    else do
      lift $ writeOut (fileOnlyPos "") $ "The following claims could not be shown to hold:"
      lift $ mapM_ (\t -> writeOut (taskPos t) $ pretty $ conjecture t) (proveGoalsTimeout proveOut)
  if length (proveGoalsFailed proveOut) == 0 then pure ()
    else do
      lift $ writeOut (fileOnlyPos "") $ "The following claims do not follow from the axioms:"
      lift $ mapM_ (\t -> writeOut (taskPos t) $ pretty $ conjecture t) (proveGoalsFailed proveOut)
  pure proveOut

proveFOL :: (MonadIO m, RunProver m, Comm m, CacheStorage m) 
  => [Prover] -> [ProofText] -> [Instr] -> Times m Exit.ExitCode
proveFOL provers txts opts0 = do
  beginTimedSection CheckTime
  typed <- lift $ typecheck =<< transform txts
  endTimedSection CheckTime
  
  beginTimedSection OntoTime
  proveTasks provers (ontologicalTasks typed) opts0
  endTimedSection OntoTime
  
  beginTimedSection ProvingTime
  let numberOfSections = length typed
  proveOut <- proveTasks provers (proofTasks typed) opts0
  endTimedSection ProvingTime

  let numberOfNotSuccessful = length (proveGoalsFailed proveOut ++ proveGoalsTimeout proveOut) 
  let numberProved = proveGoalsSentToATP proveOut - numberOfNotSuccessful
  
  let checkConsistency = askFlag CheckConsistency True opts0
  case (checkConsistency, proveFirstContradiction proveOut) of
    (True, Just t) -> lift $ writeOut (taskPos t) $
      "Ouch, there is a contradiction in your axioms!" <> softline
      <> "It was first found in the claim:" <> softline
      <> pretty (conjecture t) <> hardline
      <> "Make sure you are in a proof by contradiction by writing 'Assume the contrary.'"
    _ -> lift $ outputMain TRACING noSourcePos $
      "sections "       ++ show numberOfSections
      ++ " - goals "    ++ show (proveGoalsSentToATP proveOut)
      ++ (if numberOfNotSuccessful == 0
              then ""
              else " - failed "   ++ show numberOfNotSuccessful)
      ++ " - proved "    ++ show numberProved
      ++ " - cached "    ++ show (proveGoalsCached proveOut)

  getTimes >>= lift . showTimes
  pure $ if numberOfNotSuccessful == 0 && (not checkConsistency || isNothing (proveFirstContradiction proveOut))
    then Exit.ExitSuccess else Exit.ExitFailure 1

parseArgs :: [String] -> ([Instr], [String], [String])
parseArgs = GetOpt.getOpt GetOpt.Permute options

-- | Command line parsing
readArgs :: (Comm m, MonadIO m) => [(Pos, Instr)] -> [String] -> m ([(Pos, Instr)], ParserKind, Maybe FilePath)
readArgs initialOpts files = do
  let revInitialOpts = reverse initialOpts
  let useTexArg = askFlag UseTex False $ map snd revInitialOpts
  fileName <- case files of
    [file] -> pure $ Just file
    [] -> pure Nothing
    _ -> errorMain noSourcePos "More than one file argument\n"
  let parserKind = if useTexArg || maybe False (\f -> ".tex.ftl" `isSuffixOf` f || ".ftl.tex" `isSuffixOf` f) fileName 
      then Tex else NonTex
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
  GetOpt.Option "" ["server"] (GetOpt.NoArg (SetFlag Server True))
    "run in server mode",
  GetOpt.Option ""  ["library"] (GetOpt.ReqArg (GetArgument Library . Text.pack) "DIR")
    "place to look for library texts (def: lib)",
  GetOpt.Option ""  ["provers"] (GetOpt.ReqArg (GetArgument Provers . Text.pack) "FILE")
    "index of provers (def: provers.json)",
  GetOpt.Option "P" ["prover"] (GetOpt.ReqArg (GetArgument UseProver . Text.pack) "NAME")
    "use prover NAME (def: first listed)",
  GetOpt.Option "" ["prover-server-port"] (GetOpt.ReqArg (GetArgument ProverServerPort . Text.pack) "NAME")
    "prover server port (on localhost)",
  GetOpt.Option "" ["prover-server-password"] (GetOpt.ReqArg (GetArgument ProverServerPassword . Text.pack) "UUID")
    "prover server password",
  GetOpt.Option "t" ["timelimit"] (GetOpt.ReqArg (LimitBy Timelimit . getLeadingPositiveInt) "N")
    "N seconds per prover call (def: 3)",
  GetOpt.Option "m" ["memorylimit"] (GetOpt.ReqArg (LimitBy Memorylimit . getLeadingPositiveInt) "N")
    "maximum N MiB of memory usage per prover call (def: 2048)",
  GetOpt.Option "" ["skipfail"] (GetOpt.ReqArg (SetFlag Skipfail . parseConsent) "{on|off}")
    "ignore failed goals (def: off)",
  GetOpt.Option "" ["printgoal"] (GetOpt.ReqArg (SetFlag Printgoal . parseConsent) "{on|off}")
    "print current goal (def: on)",
  GetOpt.Option "" ["printprover"] (GetOpt.ReqArg (SetFlag Printprover . parseConsent) "{on|off}")
    "print prover's messages (def: off)",
  GetOpt.Option "" ["dump"]
    (GetOpt.ReqArg (SetFlag Dump . parseConsent) "{on|off}")
    "print tasks in prover's syntax (def: off)",
  GetOpt.Option "" ["tex"]
    (GetOpt.ReqArg (SetFlag UseTex . parseConsent) "{on|off}")
    "parse passed file with forthel tex parser (def: off)",
  GetOpt.Option "" ["fof"]
    (GetOpt.ReqArg (SetFlag UseFOF . parseConsent) "{on|off}")
    "use FOF instead of TF0 as output. Should only be used when necessary for older provers (def: off)."
  ]

parseConsent :: String -> Bool
parseConsent "yes" = True ; parseConsent "on"  = True
parseConsent "no"  = False; parseConsent "off" = False
parseConsent s     = errorWithoutStackTrace $ "Invalid boolean argument: \"" ++ s ++ "\""

getLeadingPositiveInt :: String -> Int
getLeadingPositiveInt s = case reads s of
  ((n, []) : _) | n >= 0 -> n
  _ -> errorWithoutStackTrace $ "Invalid integer argument: \"" ++ s ++ "\""
