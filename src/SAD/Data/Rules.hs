{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.Rules
-- Description : TODO
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
module SAD.Data.Rules where

import Isabelle.Bytes (Bytes)

import SAD.Data.Formula (Formula)
import SAD.Export.Presentation


data Rule = Rule {
  left :: Formula,   -- left side
  right :: Formula,   -- right side
  condition :: [Formula], -- conditions
  label :: Bytes }   -- label

instance Presentation Rule where
  present rl =
    present (left rl) <> " = " <> present (right rl) <>
    ", Cond: " <> present (condition rl) <> ", Label: " <> label rl
