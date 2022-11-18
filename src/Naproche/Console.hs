-- |
-- Authors: Makarius Wenzel (2021)
--
-- Access to physical console.


module Naproche.Console (
  setup,
  stdout,
  stderr,
  exit
) where

import System.IO qualified as IO
import System.Exit qualified as Exit

import Isabelle.UTF8 qualified as UTF8
import Isabelle.Library


setup :: IO ()
setup = do
  UTF8.setup3 IO.stdin IO.stdout IO.stderr
  IO.hSetBuffering IO.stdout IO.LineBuffering
  IO.hSetBuffering IO.stderr IO.LineBuffering

stdout :: STRING a => a -> IO ()
stdout = IO.putStrLn . make_string

stderr :: STRING a => a -> IO ()
stderr = IO.hPutStrLn IO.stderr . make_string

exit :: Int -> IO a
exit 0 = Exit.exitSuccess
exit rc = Exit.exitWith $ Exit.ExitFailure rc
