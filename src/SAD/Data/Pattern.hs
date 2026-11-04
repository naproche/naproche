{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.Pattern
-- Description : TODO
-- Copyright   : (c) 2019, Anton Lorenzen
--               (c) 2026, Marcel Schütz
-- License     : GPL-3
module SAD.Data.Pattern (
  Pattern,
  PatternComp(..),
  showSymbolPattern,
  showWordPattern
) where

import Data.Text (Text)
import Data.Text qualified as Text

type Pattern = [PatternComp]

data PatternComp
  = Word [Text]
  | Symbol Text
  | Vr
  | Nm
  deriving (Eq, Ord, Show)

showSymbolPattern :: Pattern -> Text
showSymbolPattern = foldr ((<>) . showSymbolPatternComp) ""

showSymbolPatternComp :: PatternComp -> Text
showSymbolPatternComp (Word []) = error "Empty synonym list"
showSymbolPatternComp (Word (word : _)) = word
showSymbolPatternComp (Symbol symbol) = symbol
showSymbolPatternComp Nm = "."
showSymbolPatternComp Vr = "."

showWordPattern :: Pattern -> Text
showWordPattern = foldr ((<>) . showWordPatternComp) ""

showWordPatternComp :: PatternComp -> Text
showWordPatternComp (Word []) = error "Empty synonym list"
showWordPatternComp (Word (word : _)) = Text.toTitle word
showWordPatternComp (Symbol symbol) = symbol
showWordPatternComp Nm = ""
showWordPatternComp Vr = ""
