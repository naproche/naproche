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
import SAD.Export.Pretty


data Rule = Rule {
  left :: Formula,   -- left side
  right :: Formula,   -- right side
  condition :: [Formula], -- conditions
  label :: Bytes }   -- label

instance Pretty Rule where
  pretty_print rl =
    pretty_print (left rl) <> " = " <> pretty_print (right rl) <>
    ", Cond: " <> pretty_print (condition rl) <> ", Label: " <> label rl
