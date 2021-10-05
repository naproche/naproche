{-
Authors: Makarius Wenzel (2021)

Access to physical console.
-}

module Naproche.Console (
  setup, stdout, stderr
)
where

import qualified System.IO as IO

import qualified Isabelle.UTF8 as UTF8
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
