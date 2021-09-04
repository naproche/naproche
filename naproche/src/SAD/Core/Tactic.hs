{-# LANGUAGE OverloadedStrings #-}

-- | Create proof tasks from statements.
-- This will evaluate tactics and create the necessary
-- statements for the prover.
-- Is a statement like $1 / 0 = 1 / 0$ true?
-- An ATP would say yes, but a mathematician would say no.
-- Therefore we check preconditions of definitions when they are used.
-- This is called ontological checking.

module SAD.Core.Tactic (proofTasks, ontologicalTasks) where

import Prelude hiding (error)

import SAD.Core.Typed
import SAD.Core.Task

ontologicalTasks :: [Located Stmt] -> [Task]
ontologicalTasks _ = [] 

proofTasks :: [Located Stmt] -> [Task]
proofTasks _ = []