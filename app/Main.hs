{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Main application entry point: console or server mode.
-}

{-# LANGUAGE TupleSections #-}

module Main where

import Data.Maybe
import Data.IORef
import Data.Time
import Control.Monad (when, unless)
import qualified System.Console.GetOpt as GetOpt
import qualified System.Environment as Environment
import qualified System.Exit as Exit
import qualified Control.Exception as Exception
import System.IO (IO)
import qualified System.IO as IO

import qualified Isabelle.File as File
import qualified Isabelle.Server as Server
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Properties as Properties
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML
import qualified Isabelle.UUID as UUID
import qualified Isabelle.Standard_Thread as Standard_Thread
import qualified Isabelle.Naproche as Naproche
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.ByteString.Char8 as Char8
import qualified Data.ByteString as ByteString
import Network.Socket (Socket)

import SAD.API

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
  (opts0, text0) <- readArgs args0

  oldTextRef <- newIORef $ TextRoot []

  if askFlag Help False opts0 then
    putStr (GetOpt.usageInfo usageHeader options)
  else -- main body with explicit error handling, notably for PIDE
    Exception.catch
      (if askFlag Server False opts0 then
        Server.server (Server.publish_stdout "Naproche-SAD") (serverConnection oldTextRef args0)
      else do consoleThread; mainBody oldTextRef (opts0, text0))
      (\err -> do
        exitThread
        let msg = Exception.displayException (err :: Exception.SomeException)
        IO.hPutStrLn IO.stderr msg
        Exit.exitFailure)

mainBody :: IORef Text -> ([Instr], [Text]) -> IO ()
mainBody oldTextRef (opts0, text0) = do
  startTime <- getCurrentTime

  oldText <- readIORef oldTextRef
  -- parse input text
  text1 <- fmap TextRoot $ readText (askArgument Library "." opts0) text0


  -- if -T / --onlytranslate is passed as an option, only print the translated text
  if askFlag OnlyTranslate False opts0 then
    do
      let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
          TextRoot txts = text1
      mapM_ (\case TextBlock bl -> print bl; _ -> return ()) txts

      -- print statistics
      finishTime <- getCurrentTime
      outputMain TRACING noSourcePos $ "total " ++ timeDifference finishTime
  else
    do
      -- read provers.dat
      provers <- readProverDatabase (askArgument Provers "provers.dat" opts0)
      -- initialize reasoner state
      reasonerState <- newIORef (RState [] False False)

      proveStart <- getCurrentTime

      success <- case findParseError text1 of
        Nothing -> do
          let text = textToCheck oldText text1
          (success, newText) <- verify (askArgument File "" opts0) provers reasonerState text
          case newText of
            Just txt -> writeIORef oldTextRef txt
            _ -> return ()
          pure success
        Just err -> do errorParser (errorPos err) (show err); pure False

      finishTime <- getCurrentTime
      finalReasonerState <- readIORef reasonerState

      let counterList = counters finalReasonerState
          accumulate  = accumulateIntCounter counterList 0

      -- print statistics
      outputMain TRACING noSourcePos $
        "sections "       ++ show (accumulate Sections)
        ++ " - goals "    ++ show (accumulate Goals)
        ++ (let ignoredFails = accumulate FailedGoals
            in  if   ignoredFails == 0
                then ""
                else " - failed "   ++ show ignoredFails)
        ++ " - trivial "   ++ show (accumulate TrivialGoals)
        ++ " - proved "    ++ show (accumulate SuccessfulGoals)
        ++ " - equations " ++ show (accumulate Equations)
        ++ (let failedEquations = accumulate FailedEquations
            in  if   failedEquations == 0
                then ""
                else " - failed " ++ show failedEquations)

      let trivialChecks = accumulate TrivialChecks

      outputMain TRACING noSourcePos $
        "symbols "        ++ show (accumulate Symbols)
        ++ " - checks "   ++ show
          (accumulateIntCounter counterList trivialChecks HardChecks)
        ++ " - trivial "  ++ show trivialChecks
        ++ " - proved "   ++ show (accumulate SuccessfulChecks)
        ++ " - unfolds "  ++ show (accumulate Unfolds)

      let accumulateTime = accumulateTimeCounter counterList
          proverTime     = accumulateTime proveStart ProofTime
          simplifyTime   = accumulateTime proverTime SimplifyTime

      outputMain TRACING noSourcePos $
        "parser "           ++ showTimeDiff (diffUTCTime proveStart startTime)
        ++ " - reasoner "   ++ showTimeDiff (diffUTCTime finishTime simplifyTime)
        ++ " - simplifier " ++ showTimeDiff (diffUTCTime simplifyTime proverTime)
        ++ " - prover "     ++ showTimeDiff (diffUTCTime proverTime proveStart)
        ++ "/" ++ showTimeDiff (maximalTimeCounter counterList SuccessTime)
      outputMain TRACING noSourcePos $
        "total "
        ++ showTimeDiff (diffUTCTime finishTime startTime)
      when (not success) Exit.exitFailure


serverConnection :: IORef Text -> [String] -> Socket -> IO ()
serverConnection oldTextRef args0 connection = do
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
          (opts1, text0) <- readArgs (args0 ++ args1)
          let text1 = text0 ++ [TextInstr noPos (GetArgument Text (XML.content_of body))]

          Exception.catch (mainBody oldTextRef (opts1, text1))
            (\err -> do
              let msg = Exception.displayException (err :: Exception.SomeException)
              Exception.catch
                (if YXML.detect msg then
                  Byte_Message.write connection [UTF8.fromString msg]
                 else outputMain ERROR noSourcePos msg)
                (\err2 -> do
                  let e = err2 :: Exception.IOException
                  return ())))

    _ -> return ()


-- Command line parsing

readArgs :: [String] -> IO ([Instr], [Text])
readArgs args = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args

  let fail msgs = errorWithoutStackTrace (unlines (map trimLine msgs))
  unless (null errs) $ fail errs
  when (length files > 1) $ fail ["More than one file argument\n"]
  let commandLine = case files of [file] -> instrs ++ [GetArgument File file]; _ -> instrs

  initFile <- readInit (askArgument Init "init.opt" commandLine)
  let initialOpts = initFile ++ map (noPos,) commandLine

  let revInitialOpts = map snd $ reverse initialOpts
  let initialText = map (uncurry TextInstr) initialOpts
  return (revInitialOpts, initialText)

usageHeader :: [Char]
usageHeader =
  "\nUsage: Naproche-SAD <options...> <file...>\n\n  At most one file argument may be given; \"\" refers to stdin.\n\n  Options are:\n"

options :: [GetOpt.OptDescr Instr]
options = [
  GetOpt.Option "h" ["help"] (GetOpt.NoArg (SetFlag Help True)) "show command-line help",
  GetOpt.Option ""  ["init"] (GetOpt.ReqArg (GetArgument Init) "FILE")
    "init file, empty to skip (def: init.opt)",
  GetOpt.Option "T" ["onlytranslate"] (GetOpt.NoArg (SetFlag OnlyTranslate True))
    "translate input text and exit",
  GetOpt.Option "" ["translate"] (GetOpt.ReqArg (SetFlag Translation . parseConsent) "{on|off}")
    "print first-order translation of sentences",
  GetOpt.Option "" ["server"] (GetOpt.NoArg (SetFlag Server True))
    "run in server mode",
  GetOpt.Option ""  ["library"] (GetOpt.ReqArg (GetArgument Library) "DIR")
    "place to look for library texts (def: .)",
  GetOpt.Option ""  ["provers"] (GetOpt.ReqArg (GetArgument Provers) "FILE")
    "index of provers (def: provers.dat)",
  GetOpt.Option "P" ["prover"] (GetOpt.ReqArg (GetArgument Prover) "NAME")
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
  GetOpt.Option "" ["symsign"] (GetOpt.ReqArg (SetFlag Symsign . parseConsent) "{on|off}")
    "prevent ill-typed unification (def: on)",
  GetOpt.Option "" ["info"] (GetOpt.ReqArg (SetFlag Info . parseConsent) "{on|off}")
    "collect \"evidence\" literals (def: on)",
  GetOpt.Option "" ["thesis"] (GetOpt.ReqArg (SetFlag Thesis . parseConsent) "{on|off}")
    "maintain current thesis (def: on)",
  GetOpt.Option "" ["filter"] (GetOpt.ReqArg (SetFlag Filter . parseConsent) "{on|off}")
    "filter prover tasks (def: on)",
  GetOpt.Option "" ["skipfail"] (GetOpt.ReqArg (SetFlag Skipfail . parseConsent) "{on|off}")
    "ignore failed goals (def: off)",
  GetOpt.Option "" ["flat"] (GetOpt.ReqArg (SetFlag Flat . parseConsent) "{on|off}")
    "do not read proofs (def: off)",
  GetOpt.Option "q" [] (GetOpt.NoArg (SetFlag Verbose False))
    "print no details",
  GetOpt.Option "v" [] (GetOpt.NoArg (SetFlag Verbose True))
    "print more details (-vv, -vvv, etc)",
  GetOpt.Option "" ["printgoal"] (GetOpt.ReqArg (SetFlag Printgoal . parseConsent) "{on|off}")
    "print current goal (def: on)",
  GetOpt.Option "" ["printreason"] (GetOpt.ReqArg (SetFlag Printreason . parseConsent) "{on|off}")
    "print reasoner's messages (def: off)",
  GetOpt.Option "" ["printsection"] (GetOpt.ReqArg (SetFlag Printsection . parseConsent) "{on|off}")
    "print sentence translations (def: off)",
  GetOpt.Option "" ["printcheck"] (GetOpt.ReqArg (SetFlag Printcheck . parseConsent) "{on|off}")
    "print checker's messages (def: off)",
  GetOpt.Option "" ["printprover"] (GetOpt.ReqArg (SetFlag Printprover . parseConsent) "{on|off}")
    "print prover's messages (def: off)",
  GetOpt.Option "" ["printunfold"] (GetOpt.ReqArg (SetFlag Printunfold . parseConsent) "{on|off}")
    "print definition unfoldings (def: off)",
  GetOpt.Option "" ["printfulltask"] (GetOpt.ReqArg (SetFlag Printfulltask . parseConsent) "{on|off}")
    "print full prover tasks (def: off)",
  GetOpt.Option "" ["printsimp"] (GetOpt.ReqArg (SetFlag Printsimp . parseConsent) "{on|off}")
    "print simplification process (def: off)",
  GetOpt.Option "" ["printthesis"] (GetOpt.ReqArg (SetFlag Printthesis . parseConsent) "{on|off}")
    "print thesis development (def: off)",
  GetOpt.Option "" ["ontored"] (GetOpt.ReqArg (SetFlag Ontored . parseConsent) "{on|off}")
    "enable ontological reduction (def: off)",
  GetOpt.Option "" ["unfoldlow"] (GetOpt.ReqArg (SetFlag Unfoldlow . parseConsent) "{on|off}")
    "enable unfolding of definitions in the whole low level context (def: on)",
  GetOpt.Option "" ["unfold"] (GetOpt.ReqArg (SetFlag Unfold . parseConsent) "{on|off}")
    "enable unfolding of definitions (def: on)",
  GetOpt.Option "" ["unfoldsf"] (GetOpt.ReqArg (SetFlag Unfoldsf . parseConsent) "{on|off}")
    "enable unfolding of set conditions and function evaluations (def: on)",
  GetOpt.Option "" ["unfoldlowsf"] (GetOpt.ReqArg (SetFlag Unfoldlowsf . parseConsent) "{on|off}")
    "enable unfolding of set and function conditions in general (def: off)",
  GetOpt.Option "" ["checkontored"] (GetOpt.ReqArg (SetFlag Checkontored . parseConsent) "{on|off}")
    "enable ontological reduction for checking of symbols (def: off)"]

parseConsent :: String -> Bool
parseConsent "yes" = True ; parseConsent "on"  = True
parseConsent "no"  = False; parseConsent "off" = False
parseConsent s     = errorWithoutStackTrace $ "Invalid boolean argument: \"" ++  s ++ "\""

getLeadingPositiveInt :: String -> Int
getLeadingPositiveInt s = case reads s of
  ((n, []) : _) | n >= 0 -> n
  _ -> errorWithoutStackTrace $ "Invalid integer argument: \"" ++ s ++ "\""
