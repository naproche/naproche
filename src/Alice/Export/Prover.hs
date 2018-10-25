{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Run an external prover.
-}


module Alice.Export.Prover where

import Control.Monad
import Data.List
import Data.Char
import System.Exit
import System.IO
import System.IO.Error
import System.Process
import Control.Exception

import Alice.Data.Instr
import Alice.Data.Text.Context
import Alice.Export.Base
import Alice.Export.TPTP
import Alice.Export.DFG


-- Prover interface
{- exports a proof task to a prover. argument meaning:
     red -> whether to use the reduced version of a formula or not
     m   -> reasoning depth we are at at the moment
     prs -> available provers
     ins -> instructions
     cnt -> context
     gl  -> goal -}

export :: Bool -> Int -> [Prover] -> [Instr] -> [Context] -> Context
       -> IO (IO Bool)
export red m prs ins cnt gl =
  do  when (null prs) $ die "no provers"

      let prn = askIS ISprvr (prName $ head prs) ins
      -- ask whether the user gave a prover, else take the first on the list
          prr = filter ((==) prn . prName) prs

      when (null prr) $ die $ "no prover: " ++ prn

      let prv@(Prover _ lbl pth ags fmt yes nos uns) = head prr
          tlm = askII IItlim 3 ins; agl = map (setTlim tlm) ags
          -- check whether user has specified time limit for prove tasks,
          -- else make it 3 seconds
          run = runInteractiveProcess pth agl Nothing Nothing

      let dmp = case fmt of
                  TPTP  -> tptpOut
                  DFG   -> dfgOut
          tsk = dmp red prv tlm cnt gl
          -- translate the prover task into the appropriate input language

      when (askIB IBPdmp False ins) $ putStrLn tsk
      -- print the translation if it is enabled (intended only for debugging)

      seq (length tsk) $ return $
        do  (wh,rh,eh,ph) <- catch run
                $ \ e -> die $ "run error: " ++ ioeGetErrorString e

            hPutStrLn wh tsk ; hClose wh
            -- write the task to the prover input

            ofl <- hGetContents rh ; efl <- hGetContents eh
            -- get output and errors
            let lns = filter (not . null) $ lines $ ofl ++ efl
                out = map (("[" ++ lbl ++ "] ") ++) lns

            when (length lns == 0) $ die "empty response"
            when (askIB IBPprv False ins) $ mapM_ putStrLn out
            -- if the user has enabled it, print the proveroutput

            let pos = any (\ l -> any (`isPrefixOf` l) yes) lns
                neg = any (\ l -> any (`isPrefixOf` l) nos) lns
                unk = any (\ l -> any (`isPrefixOf` l) uns) lns
            -- prover response can be: positive, negative or inconclusive

            unless (pos || neg || unk) $ die "bad response"

            hClose eh ; waitForProcess ph
            -- close error handle and wait for prover to terminate

            return pos
  where
    setTlim tl ('%':'d':rs) = show tl ++ rs
    setTlim tl (s:rs)       = s : setTlim tl rs
    setTlim _ _             = []

    die s = putStrLn ("[Export] " ++ s) >> exitFailure
