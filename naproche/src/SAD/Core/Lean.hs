{-# LANGUAGE OverloadedStrings #-}

-- | Lean export
-- This converts the type-checked source to Lean expressions.
-- Currently it will fill 'sorry's at every point where a proof
-- step between two tactics is required. In the future, this should
-- be replaced with actual proof objects.

module SAD.Core.Lean where

import Data.Functor.Identity
import SAD.Core.Typed
import Data.Text.Prettyprint.Doc

toLean :: Stmt Identity () -> Doc ann
toLean _ = ""