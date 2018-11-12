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


import Alice.Core.Base
import qualified Alice.Core.Message as Message
import Alice.Core.Position
import Alice.Core.Verify
import Alice.Data.Instr (Instr)
import qualified Alice.Data.Instr as Instr
import Alice.Data.Text.Block
import Alice.Export.Base
import Alice.Import.Reader
import qualified Isabelle.File as File


{- and what is the use of a book without pictures or conversation? -}

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
  initFile <- readInit (Instr.askIS Instr.ISinit "init.opt" commandLine)

  let initialOpts = initFile ++ commandLine
      revInitialOpts = reverse initialOpts

  -- parse input text
  text <- readText (Instr.askIS Instr.ISlibr "." revInitialOpts) $ map TI initialOpts
  -- if -T is passed as an option, only print the text and exit
  when (Instr.askIB Instr.IBtext False revInitialOpts) $ onlyTranslate startTime text
  -- read provers.dat
  provers <- readProverDatabase (Instr.askIS Instr.ISprdb "provers.dat" revInitialOpts)
  -- initialize reasoner state
  reasonerState <- newIORef (RState [] [] provers)
  proveStart <- getCurrentTime

  verify (Instr.askIS Instr.ISfile "" revInitialOpts) reasonerState text

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
  mapM_ printTB text; finishTime <- getCurrentTime
  Message.outputMain Message.WRITELN noPos $ "total " ++ timeDifference finishTime
  exitSuccess
  where
    timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
    printTB (TB bl) = print bl; printTB _ = return ()


-- Command line parsing

readOpts :: IO [Instr]
readOpts  = do
  (instrs, files, errs) <- fmap (getOpt Permute options) getArgs
  let text = instrs ++ [Instr.InStr Instr.ISfile $ head $ files ++ [""]]
  unless (all wellformed instrs && null errs)
    (putStr (concatMap ("[Main] " ++) errs) >> exitFailure)
  when (Instr.askIB Instr.IBhelp False instrs)
    (putStr (usageInfo usageHeader options) >> exitSuccess)
  return text

wellformed (Instr.InBin _ v) = v == v
wellformed (Instr.InInt _ v) = v == v
wellformed _            = True

usageHeader  = "Usage: alice <options...> <file>"

options = [
  Option "h" ["help"] (NoArg (Instr.InBin Instr.IBhelp True)) "show this help text",
  Option ""  ["init"] (ReqArg (Instr.InStr Instr.ISinit) "FILE")
    "init file, empty to skip (def: init.opt)",
  Option "T" [] (NoArg (Instr.InBin Instr.IBtext True))
    "translate input text and exit",
  Option ""  ["library"] (ReqArg (Instr.InStr Instr.ISlibr) "DIR")
    "place to look for library texts (def: .)",
  Option ""  ["provers"] (ReqArg (Instr.InStr Instr.ISprdb) "FILE")
    "index of provers (def: provers.dat)",
  Option "P" ["prover"] (ReqArg (Instr.InStr Instr.ISprvr) "NAME")
    "use prover NAME (def: first listed)",
  Option "t" ["timelimit"] (ReqArg (Instr.InInt Instr.IItlim . number) "N")
    "N seconds per prover call (def: 3)",
  Option ""  ["depthlimit"] (ReqArg (Instr.InInt Instr.IIdpth . number) "N")
    "N reasoner loops per goal (def: 7)",
  Option ""  ["checktime"] (ReqArg (Instr.InInt Instr.IIchtl . number) "N")
    "timelimit for checker's tasks (def: 1)",
  Option ""  ["checkdepth"] (ReqArg (Instr.InInt Instr.IIchdp . number) "N")
    "depthlimit for checker's tasks (def: 3)",
  Option "n" [] (NoArg (Instr.InBin Instr.IBprov False))
    "cursory mode (equivalent to --prove off)",
  Option "r" [] (NoArg (Instr.InBin Instr.IBchck False))
    "raw mode (equivalent to --check off)",
  Option "" ["prove"] (ReqArg (Instr.InBin Instr.IBprov . binary) "{on|off}")
    "prove goals in the text (def: on)",
  Option "" ["check"] (ReqArg (Instr.InBin Instr.IBchck . binary) "{on|off}")
    "check symbols for definedness (def: on)",
  Option "" ["symsign"] (ReqArg (Instr.InBin Instr.IBsign . binary) "{on|off}")
    "prevent ill-typed unification (def: on)",
  Option "" ["info"] (ReqArg (Instr.InBin Instr.IBinfo . binary) "{on|off}")
    "collect \"evidence\" literals (def: on)",
  Option "" ["thesis"] (ReqArg (Instr.InBin Instr.IBthes . binary) "{on|off}")
    "maintain current thesis (def: on)",
  Option "" ["filter"] (ReqArg (Instr.InBin Instr.IBfilt . binary) "{on|off}")
    "filter prover tasks (def: on)",
  Option "" ["skipfail"] (ReqArg (Instr.InBin Instr.IBskip . binary) "{on|off}")
    "ignore failed goals (def: off)",
  Option "" ["flat"] (ReqArg (Instr.InBin Instr.IBflat . binary) "{on|off}")
    "do not read proofs (def: off)",
  Option "q" [] (NoArg (Instr.InBin Instr.IBverb False))
    "print no details",
  Option "v" [] (NoArg (Instr.InBin Instr.IBverb True))
    "print more details (-vv, -vvv, etc)",
  Option "" ["printgoal"] (ReqArg (Instr.InBin Instr.IBPgls . binary) "{on|off}")
    "print current goal (def: on)",
  Option "" ["printreason"] (ReqArg (Instr.InBin Instr.IBPrsn . binary) "{on|off}")
    "print reasoner's messages (def: off)",
  Option "" ["printsection"] (ReqArg (Instr.InBin Instr.IBPsct . binary) "{on|off}")
    "print sentence translations (def: off)",
  Option "" ["printcheck"] (ReqArg (Instr.InBin Instr.IBPchk . binary) "{on|off}")
    "print checker's messages (def: off)",
  Option "" ["printprover"] (ReqArg (Instr.InBin Instr.IBPprv . binary) "{on|off}")
    "print prover's messages (def: off)",
  Option "" ["printunfold"] (ReqArg (Instr.InBin Instr.IBPunf . binary) "{on|off}")
    "print definition unfoldings (def: off)",
  Option "" ["printfulltask"] (ReqArg (Instr.InBin Instr.IBPtsk . binary) "{on|off}")
    "print full prover tasks (def: off)",
  Option "" ["printsimp"] (ReqArg (Instr.InBin Instr.IBPsmp . binary) "{on|off}")
    "print simplification process (def: off)",
  Option "" ["printthesis"] (ReqArg (Instr.InBin Instr.IBPths . binary) "{on|off}")
    "print thesis development (def: off)",
  Option "" ["ontored"] (ReqArg (Instr.InBin Instr.IBOnto . binary) "{on|off}")
    "enable ontological reduction (def: off)",
  Option "" ["unfoldlow"] (ReqArg (Instr.InBin Instr.IBUfdl . binary) "{on|off}")
    "enable unfolding of definitions in the whole low level context (def: on)",
  Option "" ["unfold"] (ReqArg (Instr.InBin Instr.IBUnfl . binary) "{on|off}")
    "enable unfolding of definitions (def: on)",
  Option "" ["unfoldsf"] (ReqArg (Instr.InBin Instr.IBUnfs . binary) "{on|off}")
    "enable unfolding of set conditions and function evaluations (def: on)",
  Option "" ["unfoldlowsf"] (ReqArg (Instr.InBin Instr.IBUfds . binary) "{on|off}")
    "enable unfolding of set and function conditions in general (def: off)",
  Option "" ["checkontored"] (ReqArg (Instr.InBin Instr.IBOnch . binary) "{on|off}")
    "enable ontological reduction for checking of symbols (def: off)"]

binary "yes" = True ; binary "on"  = True
binary "no"  = False; binary "off" = False
binary s     = error $ "invalid boolean argument: " ++ s

number s = case reads s of
  ((n,[]):_) | n >= 0 -> n
  _ -> error $ "invalid numeric argument: " ++ s
