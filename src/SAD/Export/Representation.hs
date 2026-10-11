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
  commaSeparated
) where

import Data.Text (Text)
import Data.Text qualified as Text


class Representation a where
  represent :: a -> Text

buildParens :: Text -> Text
buildParens xs = "(" <> xs <> ")"

buildArgumentsWith :: (a -> Text) -> [a] -> Text
buildArgumentsWith _ [] = ""
buildArgumentsWith showTerm ls = buildParens $ commaSeparated showTerm ls

commaSeparated :: (a -> Text) -> [a] -> Text
commaSeparated showTerm [] = ""
commaSeparated showTerm [t] = showTerm t
commaSeparated showTerm (t:ts) = showTerm t <> "," <> commaSeparated showTerm ts
