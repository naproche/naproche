-- |
-- Module      : SAD.Export.Representation
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.Representation (
  Representation(..),
  buildParens,
  buildArgumentsWith,
  commaSeparated,
  Builder.toLazyText
) where

import Data.Text.Lazy.Builder (Builder)
import Data.Text.Lazy.Builder qualified as Builder


class Representation a where
  represent :: a -> Builder

buildParens :: Builder -> Builder
buildParens xs = "(" <> xs <> ")"

buildArgumentsWith :: (a -> Builder) -> [a] -> Builder
buildArgumentsWith _ [] = ""
buildArgumentsWith showTerm ls = buildParens $ commaSeparated showTerm ls

commaSeparated :: (a -> Builder) -> [a] -> Builder
commaSeparated showTerm [] = ""
commaSeparated showTerm [t] = showTerm t
commaSeparated showTerm (t:ts) = showTerm t <> "," <> commaSeparated showTerm ts
