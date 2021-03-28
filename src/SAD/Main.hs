{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018),
  Anton Lorenzen (2019 - 2021)

Main application entry point: console or server mode.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Main where

import Data.List (isSuffixOf)

import qualified Data.Text as Text
import qualified System.Console.GetOpt as GetOpt
import qualified System.Exit as Exit
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Monad.State
import Data.Either (isRight)
import Data.Time (NominalDiffTime, UTCTime, getCurrentTime, diffUTCTime)

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.String (renderString)
import SAD.Core.Logging (showTimeDiff, RState(..), sumCounter, Counter(..), Tracker(..))
import SAD.Core.Message (Comm, errorParser, outputMain, Kind(..), textFieldWidth)
import SAD.Core.Provers (Prover)
import SAD.Core.Prove (RunProver(..), verify)
import SAD.Core.Reader (readProofText, HasLibrary(..))
import SAD.Core.SourcePos (noSourcePos, fileOnlyPos)
import SAD.Data.Text.Block (ProofText(..), findParseError)
import SAD.Data.Instr (Instr(..), Flag(..), askFlag, Limit(..), Argument(..), ParserKind(..), Pos)
import SAD.Parser.Error (errorPos)
import SAD.Core.Transform (convert)
import SAD.Core.Typed (located)
import SAD.Core.Cache (CacheStorage)
import SAD.Core.Task (generateTasks)

data TimedSection = ParsingTime | ProvingTime | CheckTime
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
        then showTranslation txts
        else do proveFOL provers txts opts0

showTimes :: (Comm m) => Map TimedSection NominalDiffTime -> m ()
showTimes times = do
  outputMain TRACING noSourcePos $ Text.unpack $
    "parser "           <> showTimeDiff (times Map.! ParsingTime)
    <> " - checker "     <> showTimeDiff (times Map.! CheckTime)
    <> " - prover "     <> showTimeDiff (times Map.! ProvingTime)

  outputMain TRACING noSourcePos $ Text.unpack $
    "total " <> showTimeDiff ((times Map.! ParsingTime) + (times Map.! CheckTime) + (times Map.! ProvingTime))

showTranslation :: (MonadIO m, RunProver m, Comm m, CacheStorage m)
  => [ProofText] -> Times m Exit.ExitCode
showTranslation txts = do
  beginTimedSection CheckTime
  let out = outputMain WRITELN (fileOnlyPos "")
  -- lift $ mapM_ (\case (ProofTextBlock b) -> out $ show b; _ -> pure ()) txts
  converted <- lift $ convert txts
  w <- lift $ textFieldWidth
  lift $ mapM_ (out . (++"\n") . renderString . layoutSmart
    (defaultLayoutOptions { layoutPageWidth = AvailablePerLine w 1.0 }) . pretty . located) converted
  endTimedSection CheckTime
  beginTimedSection ProvingTime
  endTimedSection ProvingTime

  -- print statistics
  getTimes >>= lift . showTimes
  pure $ Exit.ExitSuccess

proveFOL :: (MonadIO m, RunProver m, Comm m, CacheStorage m) 
  => [Prover] -> [ProofText] -> [Instr] -> Times m Exit.ExitCode
proveFOL provers txts opts0 = do
  beginTimedSection CheckTime
  typed <- lift $ convert txts
  let tasks = generateTasks typed
  endTimedSection CheckTime
  beginTimedSection ProvingTime
  let rstate = RState [Counter SectionsCounter (length typed)] False False
  finalReasonerState <- lift $ verify provers opts0 rstate tasks
  endTimedSection ProvingTime

  let trackerList = trackers finalReasonerState
  let accumulate  = sumCounter trackerList

  -- print statistics
  lift $ outputMain TRACING noSourcePos $
    "sections "       ++ show (accumulate SectionsCounter)
    ++ " - goals "    ++ show (accumulate GoalsCounter)
    ++ (let ignoredFails = accumulate FailedGoalsCounter
        in  if   ignoredFails == 0
            then ""
            else " - failed "   ++ show ignoredFails)
    ++ " - proved "    ++ show (accumulate SuccessfulGoalsCounter)
    ++ " - cached "    ++ show (accumulate CachedCounter)

  getTimes >>= lift . showTimes
  pure $ if accumulate FailedGoalsCounter == 0 then Exit.ExitSuccess else Exit.ExitFailure 1

parseArgs :: [String] -> ([Instr], [String], [String])
parseArgs = GetOpt.getOpt GetOpt.Permute options

-- | Command line parsing
readArgs :: (Comm m, MonadIO m) => [(Pos, Instr)] -> [String] -> m ([(Pos, Instr)], ParserKind, Maybe FilePath)
readArgs initialOpts files = do
  let revInitialOpts = reverse initialOpts
  let useTexArg = askFlag UseTex False $ map snd revInitialOpts
  let fileName = case files of
                  [file] -> Just file
                  [] -> Nothing
                  _ -> errorWithoutStackTrace "More than one file argument\n"
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
  GetOpt.Option "" ["translate"] (GetOpt.ReqArg (SetFlag Translation . parseConsent) "{on|off}")
    "print first-order translation of sentences",
  GetOpt.Option "" ["server"] (GetOpt.NoArg (SetFlag Server True))
    "run in server mode",
  GetOpt.Option ""  ["library"] (GetOpt.ReqArg (GetArgument Library . Text.pack) "DIR")
    "place to look for library texts (def: examples)",
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
