{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.Pattern
-- Description : TODO
-- Copyright   : (c) 2019, Anton Lorenzen
--               (c) 2026, Marcel Schütz
-- License     : GPL-3
module SAD.Data.Pattern (
  Pattern(..),
  showSymbolPatterns,
  showWordPatterns
) where

import Data.Text (Text)
import Data.Text qualified as Text

data Pattern
  = Word [Text]
  | Symbol Text
  | Vr
  | Nm
  deriving (Eq, Ord, Show)

showSymbolPatterns :: [Pattern] -> Text
showSymbolPatterns = foldr ((<>) . showSymbolPattern) ""

showSymbolPattern :: Pattern -> Text
showSymbolPattern (Word []) = error "Empty synonym list"
showSymbolPattern (Word (word : _)) = word
showSymbolPattern (Symbol symbol) = symbol
showSymbolPattern Nm = "."
showSymbolPattern Vr = "."

showWordPatterns :: [Pattern] -> Text
showWordPatterns = foldr ((<>) . showWordPattern) ""

showWordPattern :: Pattern -> Text
showWordPattern (Word []) = error "Empty synonym list"
showWordPattern (Word (word : _)) = Text.toTitle word
showWordPattern (Symbol symbol) = symbol
showWordPattern Nm = ""
showWordPattern Vr = ""
