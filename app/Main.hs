{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Main application entry point: console or server mode.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}

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

import Isabelle.Library
import qualified Isabelle.File as File
import qualified Isabelle.Server as Server
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Properties as Properties
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML
import qualified Isabelle.Naproche as Naproche
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.ByteString.Char8 as Char8
import qualified Data.ByteString as ByteString
import Network.Socket (Socket)

import SAD.Core.Base
import qualified SAD.Core.Message as Message
import SAD.Core.SourcePos
import SAD.Core.Verify
import SAD.Data.Instr (Instr)
import qualified SAD.Data.Instr as Instr
import SAD.Data.Text.Block
import SAD.Export.Base
import SAD.Import.Reader
import SAD.Parser.Error


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

  if Instr.askBool Instr.Help False opts0 then
    putStr (GetOpt.usageInfo usageHeader options)
  else -- main body with explicit error handling, notably for PIDE
    Exception.catch
      (if Instr.askBool Instr.Server False opts0 then
        Server.server (Server.publish_stdout "Naproche-SAD") (serverConnection args0)
      else do Message.consoleThread; mainBody (opts0, text0))
      (\err -> do
        Message.exitThread
        let msg = Exception.displayException (err :: Exception.SomeException)
        IO.hPutStrLn IO.stderr msg
        Exit.exitFailure)

mainBody :: ([Instr], [Text]) -> IO ()
mainBody (opts0, text0) = do
  startTime <- getCurrentTime

  -- parse input text
  text <- readText (Instr.askString Instr.Library "." opts0) text0

  -- if -T / --onlytranslate is passed as an option, only print the translated text
  if Instr.askBool Instr.OnlyTranslate False opts0 then
    do
      let timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
      mapM_ (\case TextBlock bl -> print bl; _ -> return ()) text

      -- print statistics
      finishTime <- getCurrentTime
      Message.outputMain Message.TRACING noPos $ "total " ++ timeDifference finishTime
  else
    do
      -- read provers.dat
      provers <- readProverDatabase (Instr.askString Instr.Provers "provers.dat" opts0)
      -- initialize reasoner state
      reasonerState <- newIORef (RState [] )
      proveStart <- getCurrentTime

      case checkParseCorrectness text of
        Nothing -> verify (Instr.askString Instr.File "" opts0) provers reasonerState text
        Just err -> Message.errorParser (errorPos err) (show err)

      finishTime <- getCurrentTime
      finalReasonerState <- readIORef reasonerState

      let counterList = counters finalReasonerState
          accumulate  = accumulateIntCounter counterList 0

      -- print statistics
      Message.outputMain Message.TRACING noPos $
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

      Message.outputMain Message.TRACING noPos $
        "symbols "        ++ show (accumulate Symbols)
        ++ " - checks "   ++ show
          (accumulateIntCounter counterList trivialChecks HardChecks)
        ++ " - trivial "  ++ show trivialChecks
        ++ " - proved "   ++ show (accumulate SuccessfulChecks)
        ++ " - unfolds "  ++ show (accumulate Unfolds)

      let accumulateTime = accumulateTimeCounter counterList
          proverTime     = accumulateTime proveStart ProofTime
          simplifyTime   = accumulateTime proverTime SimplifyTime

      Message.outputMain Message.TRACING noPos $
        "parser "           ++ showTimeDiff (diffUTCTime proveStart startTime)
        ++ " - reasoner "   ++ showTimeDiff (diffUTCTime finishTime simplifyTime)
        ++ " - simplifier " ++ showTimeDiff (diffUTCTime simplifyTime proverTime)
        ++ " - prover "     ++ showTimeDiff (diffUTCTime proverTime proveStart)
        ++ "/" ++ showTimeDiff (maximalTimeCounter counterList SuccessTime)
      Message.outputMain Message.TRACING noPos $
        "total "
        ++ showTimeDiff (diffUTCTime finishTime startTime)


serverConnection :: [String] -> Socket -> IO ()
serverConnection args0 connection = do
  res <- Byte_Message.read_line_message connection
  case fmap (YXML.parse . UTF8.toString) res of
    Just (XML.Elem ((command, props), body)) | command == Naproche.forthel_command -> do
      Message.initThread props (Byte_Message.write connection)

      let args1 = split_lines (the_default "" (Properties.get props Naproche.command_args))
      (opts1, text0) <- readArgs (args0 ++ args1)
      let text1 = text0 ++ [TextInstr Instr.noPos (Instr.String Instr.Text (XML.content_of body))]

      Exception.catch (mainBody (opts1, text1))
        (\err -> do
          let msg = Exception.displayException (err :: Exception.SomeException)
          if YXML.detect msg then
            Byte_Message.write connection [UTF8.fromString msg]
          else Message.outputMain Message.ERROR noPos msg)
      Message.exitThread
    _ -> return ()



-- Command line parsing

readArgs :: [String] -> IO ([Instr], [Text])
readArgs args = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args

  let fail msgs = putStr (concatMap ("[Main] " ++) msgs) >> Exit.exitFailure
  unless (all wellformed instrs && null errs) $ fail errs
  when (length files > 1) $ fail ["More than one file argument\n"]
  let commandLine = case files of [file] -> instrs ++ [Instr.String Instr.File file]; _ -> instrs

  initFile <- readInit (Instr.askString Instr.Init "init.opt" commandLine)
  let initialOpts = initFile ++ map (Instr.noPos,) commandLine

  let revInitialOpts = map snd $ reverse initialOpts
  let initialText = map (uncurry TextInstr) initialOpts

  return (revInitialOpts, initialText)

wellformed (Instr.Bool _ v) = v == v
wellformed (Instr.Int _ v) = v == v
wellformed _            = True

usageHeader =
  "\nUsage: Naproche-SAD <options...> <file...>\n\n  At most one file argument may be given; \"\" refers to stdin.\n\n  Options are:\n"

options = [
  GetOpt.Option "h" ["help"] (GetOpt.NoArg (Instr.Bool Instr.Help True)) "show command-line help",
  GetOpt.Option ""  ["init"] (GetOpt.ReqArg (Instr.String Instr.Init) "FILE")
    "init file, empty to skip (def: init.opt)",
  GetOpt.Option "T" ["onlytranslate"] (GetOpt.NoArg (Instr.Bool Instr.OnlyTranslate True))
    "translate input text and exit",
  GetOpt.Option "" ["server"] (GetOpt.NoArg (Instr.Bool Instr.Server True))
    "run in server mode",
  GetOpt.Option ""  ["library"] (GetOpt.ReqArg (Instr.String Instr.Library) "DIR")
    "place to look for library texts (def: .)",
  GetOpt.Option ""  ["provers"] (GetOpt.ReqArg (Instr.String Instr.Provers) "FILE")
    "index of provers (def: provers.dat)",
  GetOpt.Option "P" ["prover"] (GetOpt.ReqArg (Instr.String Instr.Prover) "NAME")
    "use prover NAME (def: first listed)",
  GetOpt.Option "t" ["timelimit"] (GetOpt.ReqArg (Instr.Int Instr.Timelimit . int) "N")
    "N seconds per prover call (def: 3)",
  GetOpt.Option ""  ["depthlimit"] (GetOpt.ReqArg (Instr.Int Instr.Depthlimit . int) "N")
    "N reasoner loops per goal (def: 7)",
  GetOpt.Option ""  ["checktime"] (GetOpt.ReqArg (Instr.Int Instr.Checktime . int) "N")
    "timelimit for checker's tasks (def: 1)",
  GetOpt.Option ""  ["checkdepth"] (GetOpt.ReqArg (Instr.Int Instr.Checkdepth . int) "N")
    "depthlimit for checker's tasks (def: 3)",
  GetOpt.Option "n" [] (GetOpt.NoArg (Instr.Bool Instr.Prove False))
    "cursory mode (equivalent to --prove off)",
  GetOpt.Option "r" [] (GetOpt.NoArg (Instr.Bool Instr.Check False))
    "raw mode (equivalent to --check off)",
  GetOpt.Option "" ["prove"] (GetOpt.ReqArg (Instr.Bool Instr.Prove . bool) "{on|off}")
    "prove goals in the text (def: on)",
  GetOpt.Option "" ["check"] (GetOpt.ReqArg (Instr.Bool Instr.Check . bool) "{on|off}")
    "check symbols for definedness (def: on)",
  GetOpt.Option "" ["symsign"] (GetOpt.ReqArg (Instr.Bool Instr.Symsign . bool) "{on|off}")
    "prevent ill-typed unification (def: on)",
  GetOpt.Option "" ["info"] (GetOpt.ReqArg (Instr.Bool Instr.Info . bool) "{on|off}")
    "collect \"evidence\" literals (def: on)",
  GetOpt.Option "" ["thesis"] (GetOpt.ReqArg (Instr.Bool Instr.Thesis . bool) "{on|off}")
    "maintain current thesis (def: on)",
  GetOpt.Option "" ["filter"] (GetOpt.ReqArg (Instr.Bool Instr.Filter . bool) "{on|off}")
    "filter prover tasks (def: on)",
  GetOpt.Option "" ["skipfail"] (GetOpt.ReqArg (Instr.Bool Instr.Skipfail . bool) "{on|off}")
    "ignore failed goals (def: off)",
  GetOpt.Option "" ["flat"] (GetOpt.ReqArg (Instr.Bool Instr.Flat . bool) "{on|off}")
    "do not read proofs (def: off)",
  GetOpt.Option "q" [] (GetOpt.NoArg (Instr.Bool Instr.Verbose False))
    "print no details",
  GetOpt.Option "v" [] (GetOpt.NoArg (Instr.Bool Instr.Verbose True))
    "print more details (-vv, -vvv, etc)",
  GetOpt.Option "" ["printgoal"] (GetOpt.ReqArg (Instr.Bool Instr.Printgoal . bool) "{on|off}")
    "print current goal (def: on)",
  GetOpt.Option "" ["printreason"] (GetOpt.ReqArg (Instr.Bool Instr.Printreason . bool) "{on|off}")
    "print reasoner's messages (def: off)",
  GetOpt.Option "" ["printsection"] (GetOpt.ReqArg (Instr.Bool Instr.Printsection . bool) "{on|off}")
    "print sentence translations (def: off)",
  GetOpt.Option "" ["printcheck"] (GetOpt.ReqArg (Instr.Bool Instr.Printcheck . bool) "{on|off}")
    "print checker's messages (def: off)",
  GetOpt.Option "" ["printprover"] (GetOpt.ReqArg (Instr.Bool Instr.Printprover . bool) "{on|off}")
    "print prover's messages (def: off)",
  GetOpt.Option "" ["printunfold"] (GetOpt.ReqArg (Instr.Bool Instr.Printunfold . bool) "{on|off}")
    "print definition unfoldings (def: off)",
  GetOpt.Option "" ["printfulltask"] (GetOpt.ReqArg (Instr.Bool Instr.Printfulltask . bool) "{on|off}")
    "print full prover tasks (def: off)",
  GetOpt.Option "" ["printsimp"] (GetOpt.ReqArg (Instr.Bool Instr.Printsimp . bool) "{on|off}")
    "print simplification process (def: off)",
  GetOpt.Option "" ["printthesis"] (GetOpt.ReqArg (Instr.Bool Instr.Printthesis . bool) "{on|off}")
    "print thesis development (def: off)",
  GetOpt.Option "" ["ontored"] (GetOpt.ReqArg (Instr.Bool Instr.Ontored . bool) "{on|off}")
    "enable ontological reduction (def: off)",
  GetOpt.Option "" ["unfoldlow"] (GetOpt.ReqArg (Instr.Bool Instr.Unfoldlow . bool) "{on|off}")
    "enable unfolding of definitions in the whole low level context (def: on)",
  GetOpt.Option "" ["unfold"] (GetOpt.ReqArg (Instr.Bool Instr.Unfold . bool) "{on|off}")
    "enable unfolding of definitions (def: on)",
  GetOpt.Option "" ["unfoldsf"] (GetOpt.ReqArg (Instr.Bool Instr.Unfoldsf . bool) "{on|off}")
    "enable unfolding of set conditions and function evaluations (def: on)",
  GetOpt.Option "" ["unfoldlowsf"] (GetOpt.ReqArg (Instr.Bool Instr.Unfoldlowsf . bool) "{on|off}")
    "enable unfolding of set and function conditions in general (def: off)",
  GetOpt.Option "" ["checkontored"] (GetOpt.ReqArg (Instr.Bool Instr.Checkontored . bool) "{on|off}")
    "enable ontological reduction for checking of symbols (def: off)"]

bool "yes" = True ; bool "on"  = True
bool "no"  = False; bool "off" = False
bool s     = errorWithoutStackTrace $ "Invalid boolean argument: " ++ quote s

int s = case reads s of
  ((n,[]):_) | n >= 0 -> n
  _ -> errorWithoutStackTrace $ "Invalid integer argument: " ++ quote s
