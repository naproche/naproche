{-# LANGUAGE OverloadedStrings #-}

-- | Create proof tasks from statements.
-- This will evaluate tactics and create the necessary
-- statements for the prover.

module SAD.Core.Task (Hypothesis(..), Task(..), taskFile) where

import Data.Functor.Identity
import Data.Text (Text)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import Data.Binary (Binary)

import SAD.Core.Typed
import Data.Text.Prettyprint.Doc
import SAD.Core.SourcePos (SourcePos, sourceFile)

data Task = Task 
  { hypothesis :: [Hypothesis] -- ^ from newest to oldest
  , conjecture :: (Term Identity ())
  , hints :: [Text] -- ^ helpful lemmata
  , taskName :: Text
  , byContradiction :: Bool -- ^ eprover can detect contradictory axioms
    -- and so we store whether we are in a proof by contradiction (where contradictory axioms are fine).
  , taskPos :: SourcePos
  } deriving (Eq, Ord, Show, Generic)
instance Hashable Task
instance Binary Task

taskFile :: Task -> FilePath
taskFile = sourceFile . taskPos

instance Pretty Task where
  pretty (Task hypo c h n bc _) = 
    "Goal \"" <> (pretty n) <> "\": " <> pretty c <> " " <> tupled (map pretty h) 
    <> (if bc then " by contradiction" else "") <> "\n"
    <> pretty hypo