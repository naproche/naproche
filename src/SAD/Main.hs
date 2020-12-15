{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Main application entry point: console or server mode.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Main where

import Control.Monad (when, unless)
import Data.Maybe (fromMaybe)
import Data.Time (UTCTime, addUTCTime, getCurrentTime, diffUTCTime)
import Data.ByteString (ByteString)

import qualified Control.Exception as Exception
import qualified Data.Text as Text
import qualified System.Console.GetOpt as GetOpt
import qualified System.Environment as Environment
import qualified System.Exit as Exit
import qualified System.IO as IO

import qualified PIDE
import PIDE.SourcePos

import SAD.Core.Pretty (pretty)
import SAD.API

main :: IO ()
main  = do
  -- setup stdin/stdout
  PIDE.setup IO.stdin
  PIDE.setup IO.stdout
  PIDE.setup IO.stderr
  IO.hSetBuffering IO.stdout IO.LineBuffering
  IO.hSetBuffering IO.stderr IO.LineBuffering

  -- command line and init file
  args0 <- Environment.getArgs
  (opts0, text0) <- readArgs args0

  if askFlag Help False opts0 then
    putStr (GetOpt.usageInfo usageHeader options)
  else -- main body with explicit error handling, notably for PIDE
    Exception.catch
      (if askFlag Server False opts0 then
        PIDE.server (PIDE.publish_stdout "Naproche-SAD")
          (PIDE.serverConnection $ \props -> \body -> do
            let args1 = lines (fromMaybe "" props)
            (opts1, text0) <- readArgs (args0 ++ args1)
            let text1 = text0 ++ [ProofTextInstr noPos (GetArgument Text (Text.pack body))]
            mainBody Nothing (opts1, text1)
          )
      else do PIDE.consoleThread; mainBody Nothing (opts0, text0))
      (\err -> do
        PIDE.exitThread
        let msg = Exception.displayException (err :: Exception.SomeException)
        IO.hPutStrLn IO.stderr msg
        Exit.exitFailure)

mainBody :: Maybe ByteString -> ([Instr], [ProofText]) -> IO ()
mainBody proversYaml (opts0, text0) = do
  startTime <- getCurrentTime

  -- parse input text
  txts <- readProofText (askArgument Library "." opts0) text0

  -- if -T / --onlytranslate is passed as an option, only print the translated text
  if askFlag OnlyTranslate False opts0
    then showTranslation txts startTime
    else do proveFOL proversYaml txts opts0 startTime

showTranslation :: [ProofText] -> UTCTime -> IO ()
showTranslation txts startTime = do
  let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
  mapM_ (\case ProofTextBlock bl -> print bl; _ -> return ()) txts
  mapM_ (putStrLn . Text.unpack . pretty) (convert txts)

  -- print statistics
  finishTime <- getCurrentTime
  PIDE.outputMain PIDE.TRACING noSourcePos $ Text.unpack $ "total " <> timeDifference finishTime

proveFOL :: Maybe ByteString -> [ProofText] -> [Instr] -> UTCTime -> IO ()
proveFOL proversYaml txts opts0 startTime = do
  -- read provers.yaml
  provers <- case proversYaml of
    Nothing -> readProverFile 
      $ Text.unpack (askArgument Provers "provers.yaml" opts0)
    Just txt -> readProverDatabase "" txt

  let reasonerState = RState [] False False
  proveStart <- getCurrentTime

  (success, finalReasonerState) <- case findParseError (ProofTextRoot txts) of
    Nothing -> do
      let typed = convert txts
      verify provers opts0 reasonerState typed
    Just err -> do 
      PIDE.errorParser (errorPos err) (show err)
      pure (False, reasonerState)

  finishTime <- getCurrentTime

  let trackerList = trackers finalReasonerState
  let accumulate  = sumCounter trackerList

  -- print statistics
  PIDE.outputMain PIDE.TRACING noSourcePos $
    "sections "       ++ show (accumulate Sections)
    ++ " - goals "    ++ show (accumulate Goals)
    ++ (let ignoredFails = accumulate FailedGoals
        in  if   ignoredFails == 0
            then ""
            else " - failed "   ++ show ignoredFails)
    ++ " - proved "    ++ show (accumulate SuccessfulGoals)

  let proverTime     = sumTimer trackerList ProofTimer
  let simplifyTime   = sumTimer trackerList SimplifyTimer
  let proveFinish    = addUTCTime proverTime proveStart
  let simplifyFinish = addUTCTime simplifyTime proveFinish

  PIDE.outputMain PIDE.TRACING noSourcePos $ Text.unpack $
    "parser "           <> showTimeDiff (diffUTCTime proveStart startTime)
    <> " - reasoner "   <> showTimeDiff (diffUTCTime finishTime simplifyFinish)
    <> " - simplifier " <> showTimeDiff simplifyTime
    <> " - prover "     <> showTimeDiff proverTime
    <> "/" <> showTimeDiff (maximalTimer trackerList SuccessTimer)

  PIDE.outputMain PIDE.TRACING noSourcePos $ Text.unpack $
    "total " <> showTimeDiff (diffUTCTime finishTime startTime)

  when (not success) Exit.exitFailure

-- Command line parsing

readArgs :: [String] -> IO ([Instr], [ProofText])
readArgs args = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args

  let fail msgs = errorWithoutStackTrace (unlines (map PIDE.trim_line msgs))
  unless (null errs) $ fail errs
  when (length files > 1) $ fail ["More than one file argument\n"]
  let commandLine = case files of [file] -> instrs ++ [GetArgument File (Text.pack file)]; _ -> instrs

  initFile <- readInit (askArgument Init "init.opt" commandLine)
  let initialOpts = initFile ++ map (noPos,) commandLine

  let revInitialOpts = map snd $ reverse initialOpts
  let initialProofText = map (uncurry ProofTextInstr) initialOpts
  return (revInitialOpts, initialProofText)

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
  GetOpt.Option "" ["new-parser"] (GetOpt.ReqArg (SetFlag NewParser . parseConsent) "{on|off}")
    "use latex parsing",
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
    "print tasks in prover's syntax (def: off)"
  ]

parseConsent :: String -> Bool
parseConsent "yes" = True ; parseConsent "on"  = True
parseConsent "no"  = False; parseConsent "off" = False
parseConsent s     = errorWithoutStackTrace $ "Invalid boolean argument: \"" ++ s ++ "\""

getLeadingPositiveInt :: String -> Int
getLeadingPositiveInt s = case reads s of
  ((n, []) : _) | n >= 0 -> n
  _ -> errorWithoutStackTrace $ "Invalid integer argument: \"" ++ s ++ "\""
