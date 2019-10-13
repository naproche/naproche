{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Prover interface: export a proof task to an external prover.
-}

module SAD.Export.Prover where

import Control.Monad (when, unless)
import Data.Maybe
import Data.List
import System.IO
import System.IO.Error
import qualified System.Process as Process
import qualified Control.Exception as Exception
import qualified Data.Text.Lazy as Text
import qualified Data.Text.Lazy.IO as TIO
import Data.Text.Lazy (Text)

import qualified Isabelle.File as File
import qualified Isabelle.Standard_Thread as Standard_Thread

import SAD.Core.SourcePos
import SAD.Data.Instr hiding (Prover)
import SAD.Data.Text.Context (Context)
import SAD.Export.Base
import SAD.Helpers (notNull)

import qualified SAD.Core.Message as Message
import qualified SAD.Data.Instr as Instr
import qualified SAD.Export.TPTP as TPTP

export :: Int -> [Prover] -> [Instr] -> [Context] -> Context -> IO Bool
export depth provers instrs context goal = do
  Standard_Thread.expose_stopped

  when (null provers) $ Message.errorExport noSourcePos "No provers"

  let proverName = Text.unpack $ askArgument Instr.Prover (Text.pack $ name $ head provers) instrs
      proversNamed = filter ((==) proverName . name) provers

  when (null proversNamed) $ 
    Message.errorExport noSourcePos $ "No prover named " ++ show proverName
  
  let printProver = askFlag Printprover False instrs
  let timeLimit = askLimit Timelimit 3 instrs
  let task = TPTP.output context goal

  when (askFlag Dump False instrs) $ 
    Message.output "" Message.WRITELN noSourcePos (Text.unpack task)

  runProver (head proversNamed) printProver task timeLimit

runUntilSuccess :: Int -> (Int -> IO Bool) -> IO Bool
runUntilSuccess timeLimit f = go $ takeWhile (<=timeLimit) $ map (4^) [(0::Int)..]
  where
    go [] = pure False
    go (x:xs) = do
      b <- f x
      if b then pure True else go xs

runProver :: Prover -> Bool -> Text -> Int -> IO Bool
runProver (Prover _ label path args yes nos uns) printProver task timeLimit = do
  let proc = (Process.proc path (map (setTimeLimit timeLimit) args))
        { Process.std_in = Process.CreatePipe
        ,  Process.std_out = Process.CreatePipe
        ,  Process.std_err = Process.CreatePipe
        ,  Process.create_group = True
        ,  Process.new_session = True}
  let process = do
        (pin, pout, perr, p) <- Process.createProcess proc
        return (fromJust pin, fromJust pout, fromJust perr, p)

  (prvin, prvout, prverr, prv) <- Exception.catch process
      (\e -> Message.errorExport noSourcePos $
        "Failed to run " ++ show path ++ ": " ++ ioeGetErrorString e)

  File.setup prvin
  File.setup prvout
  File.setup prverr

  TIO.hPutStrLn prvin task
  hClose prvin

  let terminate = do
        Process.interruptProcessGroupOf prv
        Process.waitForProcess prv
        return ()

  Standard_Thread.bracket_resource terminate $ do
    output <- hGetContents prvout
    errors <- hGetContents prverr
    let lns = filter notNull $ lines $ output ++ errors
        out = map (("[" ++ label ++ "] ") ++) lns

    when (null lns) $ Message.errorExport noSourcePos "No prover response"
    when printProver $
        mapM_ (Message.output "" Message.WRITELN noSourcePos) out

    let positive = any (\l -> any (`isPrefixOf` l) yes) lns
        negative = any (\l -> any (`isPrefixOf` l) nos) lns
        inconclusive = any (\l -> any (`isPrefixOf` l) uns) lns

    unless (positive || negative || inconclusive) $
        Message.errorExport noSourcePos $ unlines ("Bad prover response:" : lns)

    hClose prverr
    Process.waitForProcess prv

    return positive

setTimeLimit :: Int -> String -> String
setTimeLimit timeLimit ('%':'d':rs) = show timeLimit ++ rs
setTimeLimit timeLimit (s:rs) = s : setTimeLimit timeLimit rs
setTimeLimit _ _ = []