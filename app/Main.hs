{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Parse command line and run verifier.
-}

module Main where

import Data.IORef
import Data.Time
import Control.Monad
import System.Console.GetOpt
import System.Environment
import System.Exit hiding (die)
import System.IO
import qualified Control.Exception
import qualified Data.IntMap.Strict as IM


import SAD.Core.Base
import qualified SAD.Core.Message as Message
import SAD.Core.SourcePos
import SAD.Core.Verify
import SAD.Data.Instr (Instr)
import qualified SAD.Data.Instr as Instr
import SAD.Data.Text.Block
import SAD.Export.Base
import SAD.Import.Reader
import qualified Isabelle.File as File

main :: IO ()
main  = do
  -- setup stdin/stdout
  File.setup stdin
  File.setup stdout
  File.setup stderr
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering

  -- main body with explicit error handling, notably for PIDE
  Control.Exception.catch mainBody
    (\err -> hPrint stderr (err :: Control.Exception.SomeException))

mainBody :: IO ()
mainBody  = do
  startTime <- getCurrentTime

  commandLine <- readOpts
  let initFileName = Instr.askString Instr.Init "init.opt" commandLine
  initFile <- readInit initFileName

  let initialOpts = initFile ++ map (\instr -> (noRange, instr)) commandLine
      revInitialOpts = map snd $ reverse initialOpts

  -- parse input text
  text <-
    readText (Instr.askString Instr.Library "." revInitialOpts) $
    map (uncurry TextInstr) initialOpts
  -- if -T is passed as an option, only print the text and exit
  when (Instr.askBool Instr.OnlyTranslate False revInitialOpts) $ onlyTranslate startTime text
  -- read provers.dat
  provers <- readProverDatabase (Instr.askString Instr.Provers "provers.dat" revInitialOpts)
  -- initialize reasoner state
  reasonerState <- newIORef (RState [] [] provers)
  proveStart <- getCurrentTime

  verify (Instr.askString Instr.File "" revInitialOpts) reasonerState text

  finishTime <- getCurrentTime
  finalReasonerState <- readIORef reasonerState

  let counterList = counters finalReasonerState
      accumulate  = accumulateIntCounter counterList 0

  -- print statistics
  Message.outputMain Message.WRITELN noPos $
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

  Message.outputMain Message.WRITELN noPos $
    "symbols "        ++ show (accumulate Symbols)
    ++ " - checks "   ++ show
      (accumulateIntCounter counterList trivialChecks HardChecks)
    ++ " - trivial "  ++ show trivialChecks
    ++ " - proved "   ++ show (accumulate SuccessfulChecks)
    ++ " - unfolds "  ++ show (accumulate Unfolds)

  let accumulateTime = accumulateTimeCounter counterList
      proverTime     = accumulateTime proveStart ProofTime
      simplifyTime   = accumulateTime proverTime SimplifyTime

  Message.outputMain Message.WRITELN noPos $
    "parser "           ++ showTimeDiff (diffUTCTime proveStart startTime)
    ++ " - reasoner "   ++ showTimeDiff (diffUTCTime finishTime simplifyTime)
    ++ " - simplifier " ++ showTimeDiff (diffUTCTime simplifyTime proverTime)
    ++ " - prover "     ++ showTimeDiff (diffUTCTime proverTime proveStart)
    ++ "/" ++ showTimeDiff (maximalTimeCounter counterList SuccessTime)
  Message.outputMain Message.WRITELN noPos $
    "total "
    ++ showTimeDiff (diffUTCTime finishTime startTime)


onlyTranslate :: UTCTime -> [Text] -> IO ()
onlyTranslate startTime text = do
  mapM_ printTextBlock text; finishTime <- getCurrentTime
  Message.outputMain Message.WRITELN noPos $ "total " ++ timeDifference finishTime
  exitSuccess
  where
    timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
    printTextBlock (TextBlock bl) = print bl
    printTextBlock _ = return ()


-- Command line parsing

readOpts :: IO [Instr]
readOpts  = do
  (instrs, files, errs) <- fmap (getOpt Permute options) getArgs
  let text = instrs ++ [Instr.String Instr.File $ head $ files ++ [""]]
  unless (all wellformed instrs && null errs)
    (putStr (concatMap ("[Main] " ++) errs) >> exitFailure)
  when (Instr.askBool Instr.Help False instrs)
    (putStr (usageInfo usageHeader options) >> exitSuccess)
  return text

wellformed (Instr.Bool _ v) = v == v
wellformed (Instr.Int _ v) = v == v
wellformed _            = True

usageHeader  = "Usage: Naproche-SAD <options...> <file>"

options = [
  Option "h" ["help"] (NoArg (Instr.Bool Instr.Help True)) "show this help text",
  Option ""  ["init"] (ReqArg (Instr.String Instr.Init) "FILE")
    "init file, empty to skip (def: init.opt)",
  Option "T" [] (NoArg (Instr.Bool Instr.OnlyTranslate True))
    "translate input text and exit",
  Option ""  ["library"] (ReqArg (Instr.String Instr.Library) "DIR")
    "place to look for library texts (def: .)",
  Option ""  ["provers"] (ReqArg (Instr.String Instr.Provers) "FILE")
    "index of provers (def: provers.dat)",
  Option "P" ["prover"] (ReqArg (Instr.String Instr.Prover) "NAME")
    "use prover NAME (def: first listed)",
  Option "t" ["timelimit"] (ReqArg (Instr.Int Instr.Timelimit . int) "N")
    "N seconds per prover call (def: 3)",
  Option ""  ["depthlimit"] (ReqArg (Instr.Int Instr.Depthlimit . int) "N")
    "N reasoner loops per goal (def: 7)",
  Option ""  ["checktime"] (ReqArg (Instr.Int Instr.Checktime . int) "N")
    "timelimit for checker's tasks (def: 1)",
  Option ""  ["checkdepth"] (ReqArg (Instr.Int Instr.Checkdepth . int) "N")
    "depthlimit for checker's tasks (def: 3)",
  Option "n" [] (NoArg (Instr.Bool Instr.Prove False))
    "cursory mode (equivalent to --prove off)",
  Option "r" [] (NoArg (Instr.Bool Instr.Check False))
    "raw mode (equivalent to --check off)",
  Option "" ["prove"] (ReqArg (Instr.Bool Instr.Prove . bool) "{on|off}")
    "prove goals in the text (def: on)",
  Option "" ["check"] (ReqArg (Instr.Bool Instr.Check . bool) "{on|off}")
    "check symbols for definedness (def: on)",
  Option "" ["symsign"] (ReqArg (Instr.Bool Instr.Symsign . bool) "{on|off}")
    "prevent ill-typed unification (def: on)",
  Option "" ["info"] (ReqArg (Instr.Bool Instr.Info . bool) "{on|off}")
    "collect \"evidence\" literals (def: on)",
  Option "" ["thesis"] (ReqArg (Instr.Bool Instr.Thesis . bool) "{on|off}")
    "maintain current thesis (def: on)",
  Option "" ["filter"] (ReqArg (Instr.Bool Instr.Filter . bool) "{on|off}")
    "filter prover tasks (def: on)",
  Option "" ["skipfail"] (ReqArg (Instr.Bool Instr.Skipfail . bool) "{on|off}")
    "ignore failed goals (def: off)",
  Option "" ["flat"] (ReqArg (Instr.Bool Instr.Flat . bool) "{on|off}")
    "do not read proofs (def: off)",
  Option "q" [] (NoArg (Instr.Bool Instr.Verbose False))
    "print no details",
  Option "v" [] (NoArg (Instr.Bool Instr.Verbose True))
    "print more details (-vv, -vvv, etc)",
  Option "" ["printgoal"] (ReqArg (Instr.Bool Instr.Printgoal . bool) "{on|off}")
    "print current goal (def: on)",
  Option "" ["printreason"] (ReqArg (Instr.Bool Instr.Printreason . bool) "{on|off}")
    "print reasoner's messages (def: off)",
  Option "" ["printsection"] (ReqArg (Instr.Bool Instr.Printsection . bool) "{on|off}")
    "print sentence translations (def: off)",
  Option "" ["printcheck"] (ReqArg (Instr.Bool Instr.Printcheck . bool) "{on|off}")
    "print checker's messages (def: off)",
  Option "" ["printprover"] (ReqArg (Instr.Bool Instr.Printprover . bool) "{on|off}")
    "print prover's messages (def: off)",
  Option "" ["printunfold"] (ReqArg (Instr.Bool Instr.Printunfold . bool) "{on|off}")
    "print definition unfoldings (def: off)",
  Option "" ["printfulltask"] (ReqArg (Instr.Bool Instr.Printfulltask . bool) "{on|off}")
    "print full prover tasks (def: off)",
  Option "" ["printsimp"] (ReqArg (Instr.Bool Instr.Printsimp . bool) "{on|off}")
    "print simplification process (def: off)",
  Option "" ["printthesis"] (ReqArg (Instr.Bool Instr.Printthesis . bool) "{on|off}")
    "print thesis development (def: off)",
  Option "" ["ontored"] (ReqArg (Instr.Bool Instr.Ontored . bool) "{on|off}")
    "enable ontological reduction (def: off)",
  Option "" ["unfoldlow"] (ReqArg (Instr.Bool Instr.Unfoldlow . bool) "{on|off}")
    "enable unfolding of definitions in the whole low level context (def: on)",
  Option "" ["unfold"] (ReqArg (Instr.Bool Instr.Unfold . bool) "{on|off}")
    "enable unfolding of definitions (def: on)",
  Option "" ["unfoldsf"] (ReqArg (Instr.Bool Instr.Unfoldsf . bool) "{on|off}")
    "enable unfolding of set conditions and function evaluations (def: on)",
  Option "" ["unfoldlowsf"] (ReqArg (Instr.Bool Instr.Unfoldlowsf . bool) "{on|off}")
    "enable unfolding of set and function conditions in general (def: off)",
  Option "" ["checkontored"] (ReqArg (Instr.Bool Instr.Checkontored . bool) "{on|off}")
    "enable ontological reduction for checking of symbols (def: off)"]

bool "yes" = True ; bool "on"  = True
bool "no"  = False; bool "off" = False
bool s     = error $ "invalid boolean argument: " ++ s

int s = case reads s of
  ((n,[]):_) | n >= 0 -> n
  _ -> error $ "invalid integer argument: " ++ s
