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
import qualified Data.IntMap.Strict as IM


import Alice.Core.Base
import Alice.Core.Verify
import Alice.Data.Instr
import Alice.Data.Text.Block
import Alice.Export.Base
import Alice.Import.Reader

{- and what is the use of a book without pictures or conversation? -}

main :: IO ()
main  = do
  startTime <- getCurrentTime
  hSetBuffering stdout LineBuffering

  commandLine <- readOpts
  initFile <- readInit (askIS ISinit "init.opt" commandLine)

  let initialOpts = initFile ++ commandLine
      revInitialOpts = reverse initialOpts

  -- parse input text
  text <- readText (askIS ISlibr "." revInitialOpts) $ map TI initialOpts
  -- if -T is passed as an option, only print the text and exit
  when (askIB IBtext False revInitialOpts) $ onlyTranslate startTime text
  -- read provers.dat
  provers <- readPrDB (askIS ISprdb "provers.dat" revInitialOpts)
  -- initialize reasoner state
  reasonerState <- newIORef (RState [] [] provers)
  proveStart <- getCurrentTime

  verify (askIS ISfile "" revInitialOpts) reasonerState text

  finishTime <- getCurrentTime
  finalReasonerState <- readIORef reasonerState

  let counterList = counters finalReasonerState
      accumulate  = accumulateIntCounter counterList 0

  -- print statistics
  putStrLn $ "[Main] "
    ++ "sections "    ++ show (accumulate Sections)
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

  putStrLn $ "[Main] "
    ++ "symbols "     ++ show (accumulate Symbols)
    ++ " - checks "   ++ show 
      (accumulateIntCounter counterList trivialChecks HardChecks)
    ++ " - trivial "  ++ show trivialChecks
    ++ " - proved "   ++ show (accumulate SuccessfulChecks)
    ++ " - unfolds "  ++ show (accumulate Unfolds)

  let accumulateTime = accumulateTimeCounter counterList
      proverTime     = accumulateTime proveStart ProofTime
      simplifyTime   = accumulateTime proverTime SimplifyTime

  putStrLn $ "[Main] "
    ++ "parser "        ++ showTimeDiff (diffUTCTime proveStart startTime)
    ++ " - reason "     ++ showTimeDiff (diffUTCTime finishTime simplifyTime)
    ++ " - simplifier " ++ showTimeDiff (diffUTCTime simplifyTime proverTime)
    ++ " - prover "     ++ showTimeDiff (diffUTCTime proverTime proveStart)
    ++ "/" ++ showTimeDiff (maximalTimeCounter counterList SuccessTime)
  putStrLn $ "[Main] "
    ++ "total "
    ++ showTimeDiff (diffUTCTime finishTime startTime)


onlyTranslate :: UTCTime -> [Text] -> IO ()
onlyTranslate startTime text = do
  mapM_ printTB text; finishTime <- getCurrentTime
  putStrLn $ "[Main] total " ++ timeDifference finishTime
  exitSuccess
  where
    timeDifference finishTime = showTimeDiff (diffUTCTime finishTime startTime)
    printTB (TB bl) = print bl; printTB _ = return ()


-- Command line parsing

readOpts :: IO [Instr]
readOpts  = do
  (is, fs, es) <- fmap (getOpt Permute options) getArgs
  let text = is ++ [InStr ISfile $ head $ fs ++ [""]]
  unless (all wellformed is && null es) $ die es
  when (askIB IBPIDE False is) initPIDE
  when (askIB IBhelp False is) helper
  return text

wellformed (InBin _ v)  = v == v; wellformed (InInt _ v)  = v == v
wellformed _            = True

initPIDE = putStrLn "PIDE protocol init"   -- FIXME proper implementation

helper = putStr (usageInfo usageHeader options) >> exitSuccess

die es = putStr (concatMap ("[Main] " ++) es) >> exitFailure

usageHeader  = "Usage: alice <options...> <file>"

options = [
  Option "h" ["help"] (NoArg (InBin IBhelp True)) "show this help text",
  Option ""  ["init"] (ReqArg (InStr ISinit) "FILE")
    "init file, empty to skip (def: init.opt)",
  Option "T" [] (NoArg (InBin IBtext True))
    "translate input text and exit",
  Option ""  ["library"] (ReqArg (InStr ISlibr) "DIR")
    "place to look for library texts (def: .)",
  Option ""  ["provers"] (ReqArg (InStr ISprdb) "FILE")
    "index of provers (def: provers.dat)",
  Option "P" ["prover"] (ReqArg (InStr ISprvr) "NAME")
    "use prover NAME (def: first listed)",
  Option "t" ["timelimit"] (ReqArg (InInt IItlim . number) "N")
    "N seconds per prover call (def: 3)",
  Option ""  ["depthlimit"] (ReqArg (InInt IIdpth . number) "N")
    "N reasoner loops per goal (def: 7)",
  Option ""  ["checktime"] (ReqArg (InInt IIchtl . number) "N")
    "timelimit for checker's tasks (def: 1)",
  Option ""  ["checkdepth"] (ReqArg (InInt IIchdp . number) "N")
    "depthlimit for checker's tasks (def: 3)",
  Option "n" [] (NoArg (InBin IBprov False))
    "cursory mode (equivalent to --prove off)",
  Option "r" [] (NoArg (InBin IBchck False))
    "raw mode (equivalent to --check off)",
  Option "" ["prove"] (ReqArg (InBin IBprov . binary) "{on|off}")
    "prove goals in the text (def: on)",
  Option "" ["check"] (ReqArg (InBin IBchck . binary) "{on|off}")
    "check symbols for definedness (def: on)",
  Option "" ["symsign"] (ReqArg (InBin IBsign . binary) "{on|off}")
    "prevent ill-typed unification (def: on)",
  Option "" ["info"] (ReqArg (InBin IBinfo . binary) "{on|off}")
    "collect \"evidence\" literals (def: on)",
  Option "" ["thesis"] (ReqArg (InBin IBthes . binary) "{on|off}")
    "maintain current thesis (def: on)",
  Option "" ["filter"] (ReqArg (InBin IBfilt . binary) "{on|off}")
    "filter prover tasks (def: on)",
  Option "" ["skipfail"] (ReqArg (InBin IBskip . binary) "{on|off}")
    "ignore failed goals (def: off)",
  Option "" ["flat"] (ReqArg (InBin IBflat . binary) "{on|off}")
    "do not read proofs (def: off)",
  Option "q" [] (NoArg (InBin IBverb False))
    "print no details",
  Option "v" [] (NoArg (InBin IBverb True))
    "print more details (-vv, -vvv, etc)",
  Option "" ["printgoal"] (ReqArg (InBin IBPgls . binary) "{on|off}")
    "print current goal (def: on)",
  Option "" ["printreason"] (ReqArg (InBin IBPrsn . binary) "{on|off}")
    "print reasoner's messages (def: off)",
  Option "" ["printsection"] (ReqArg (InBin IBPsct . binary) "{on|off}")
    "print sentence translations (def: off)",
  Option "" ["printcheck"] (ReqArg (InBin IBPchk . binary) "{on|off}")
    "print checker's messages (def: off)",
  Option "" ["printprover"] (ReqArg (InBin IBPprv . binary) "{on|off}")
    "print prover's messages (def: off)",
  Option "" ["printunfold"] (ReqArg (InBin IBPunf . binary) "{on|off}")
    "print definition unfoldings (def: off)",
  Option "" ["printfulltask"] (ReqArg (InBin IBPtsk . binary) "{on|off}")
    "print full prover tasks (def: off)",
  Option "" ["printsimp"] (ReqArg (InBin IBPsmp . binary) "{on|off}")
    "print simplification process (def: off)",
  Option "" ["printthesis"] (ReqArg (InBin IBPths . binary) "{on|off}")
    "print thesis development (def: off)",
  Option "" ["ontored"] (ReqArg (InBin IBOnto . binary) "{on|off}")
    "enable ontological reduction (def: off)",
  Option "" ["unfoldlow"] (ReqArg (InBin IBUfdl . binary) "{on|off}")
    "enable unfolding of definitions in the whole low level context (def: on)",
  Option "" ["unfold"] (ReqArg (InBin IBUnfl . binary) "{on|off}")
    "enable unfolding of definitions (def: on)",
  Option "" ["unfoldsf"] (ReqArg (InBin IBUnfs . binary) "{on|off}")
    "enable unfolding of set conditions and function evaluations (def: on)",
  Option "" ["unfoldlowsf"] (ReqArg (InBin IBUfds . binary) "{on|off}")
    "enable unfolding of set and function conditions in general (def: off)",
  Option "" ["checkontored"] (ReqArg (InBin IBOnch . binary) "{on|off}")
    "enable ontological reduction for checking of symbols (def: off)",
  Option "" ["PIDE"] (ReqArg (InBin IBPIDE . binary) "{on|off}")
    "enable Prover IDE protocol (def: off)"]

binary "yes" = True ; binary "on"  = True
binary "no"  = False; binary "off" = False
binary s     = error $ "invalid boolean argument: " ++ s

number s = case reads s of
  ((n,[]):_) | n >= 0 -> n
  _ -> error $ "invalid numeric argument: " ++ s
