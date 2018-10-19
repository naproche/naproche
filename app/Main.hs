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
import System.Exit
import System.IO
import qualified Data.IntMap.Strict as IM


import Alice.Core.Base
import Alice.Core.Verify
import Alice.Data.Instr
import Alice.Data.Text
import Alice.Export.Base
import Alice.Import.Reader

{- and what is the use of a book without pictures or conversation? -}

main :: IO ()
main  =
  do  strt <- getCurrentTime
      hSetBuffering stdout LineBuffering

      cmdl <- readOpts -- read commandline
      cmdf <- readInit (askIS ISinit "init.opt" cmdl) --determine init file

      let inix = cmdf ++ cmdl
          xini = reverse inix

      text <- readText (askIS ISlibr "." xini) $ map TI inix -- parse the input text

      when (askIB IBtext False xini) $ trans strt text -- if -T is passed as an option, only print the text and exit

      prdb <- readPrDB (askIS ISprdb "provers.dat" xini) -- read provers
      rstt <- newIORef (RState [] [] prdb) -- initialize state
      prst <- getCurrentTime

      verify (askIS ISfile "" xini) rstt text -- verify the text

      fint <- getCurrentTime
      stat <- readIORef rstt -- get the final state

      let cntr = rsCntr stat
          eqfl = cumulCI CIeqfl 0 cntr
          igno = cumulCI CIfail 0 cntr
          subt = cumulCI CIsubt 0 cntr
          chkt = cumulCI CIchkt 0 cntr
          prvt = cumulCT CTprov prst cntr
          smpt = cumulCT CTsimp prvt cntr
      -- print statistics
      putStrLn $ "[Main] "
              ++ "sections "    ++ show (cumulCI CIsect 0 cntr)
              ++ " - goals "    ++ show (cumulCI CIgoal 0 cntr)
              ++ (if igno == 0 then "" else
                 " - failed "   ++ show igno)
              ++ " - trivial "  ++ show subt
              ++ " - proved "   ++ show (cumulCI CIprvy 0 cntr)
              ++ " - equations " ++ show (cumulCI CIeqtn 0 cntr)
              ++ (if eqfl == 0 then "" else
                  " - failed " ++ show eqfl)
      putStrLn $ "[Main] "
              ++ "symbols "     ++ show (cumulCI CIsymb 0 cntr)
              ++ " - checks "   ++ show (cumulCI CIchkh chkt cntr)
              ++ " - trivial "  ++ show chkt
              ++ " - proved "   ++ show (cumulCI CIchky 0 cntr)
              ++ " - unfolds "  ++ show (cumulCI CIunfl 0 cntr)
      putStrLn $ "[Main] "
              ++ "parser "      ++ showTimeDiff (diffUTCTime prst strt)
              ++ " - reason "   ++ showTimeDiff (diffUTCTime fint smpt)
              ++ " - simplifier "++ showTimeDiff (diffUTCTime smpt prvt)
              ++ " - prover "   ++ showTimeDiff (diffUTCTime prvt prst)
              ++ "/" ++ showTimeDiff (maximCT CTprvy cntr)
      putStrLn $ "[Main] "
              ++ "total "       ++ showTimeDiff (diffUTCTime fint strt)


trans :: UTCTime -> [Text] -> IO ()
trans strt text = do  mapM_ printTB text ; fint <- getCurrentTime
                      putStrLn $ "[Main] total " ++ tmdiff fint
                      exitWith ExitSuccess
  where
    tmdiff fint = showTimeDiff (diffUTCTime fint strt)
    printTB (TB bl) = print bl ; printTB _ = return ()


-- Command line parsing

readOpts :: IO [Instr]
readOpts  =
  do  (is, fs, es) <- liftM (getOpt Permute options) getArgs
      let text = is ++ [InStr ISfile $ head $ fs ++ [""]]
      unless (all wf is && null es) $ die es
      when (askIB IBhelp False is) helper
      return text
  where
    header  = "Usage: alice <options...> <file>"

    options =
      [ Option "h" [] (NoArg (InBin IBhelp True)) "this help",
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
            "enable unfolding of set and function conditions in the whole low level context (def: off)",
        Option "" ["checkontored"] (ReqArg (InBin IBOnch . binary) "{on|off}")
             "enable ontological reduction for checking of symbols (def: off)"]

    binary "yes"  = True
    binary "on"   = True
    binary "no"   = False
    binary "off"  = False
    binary s      = error $ "invalid boolean argument: " ++ s

    number s  = case reads s of
      ((n,[]):_) | n >= 0 -> n
      _ -> error $ "invalid numeric argument: " ++ s

    wf (InBin _ v)  = v == v
    wf (InInt _ v)  = v == v
    wf _            = True

    helper  = do  putStr $ usageInfo header options
                  exitWith ExitSuccess

    die es  = do  putStr $ concatMap ("[Main] " ++) es
                  exitFailure
