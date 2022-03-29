{-
Authors: Anton Lorenzen (2022)

Abstraction of Files for Webinterface
-}

module Naproche.File (MonadFile(..)) where

import Prelude hiding (read)
import qualified System.IO as IO
import Control.Monad.IO.Class (MonadIO)
import Isabelle.Bytes (Bytes)

class MonadIO m => MonadFile m where
  read :: IO.FilePath -> m Bytes
  write :: IO.FilePath -> Bytes -> m ()
  append :: IO.FilePath -> Bytes -> m ()