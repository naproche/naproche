{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.Representation
  ( Representation(..)
  , buildParens
  , buildArgumentsWith
  , commaSeparated
  )where

import Data.Text (Text)

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