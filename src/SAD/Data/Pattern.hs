-- |
-- Module      : SAD.Data.Pattern
-- Description : Patterns: Verbal and symbolic presentations of mathematical
--               notions, relations, functions, constants etc.
-- Copyright   : (c) 2019, Anton Lorenzen
--               (c) 2026, Marcel Schütz
-- License     : GPL-3
module SAD.Data.Pattern (
  PredicatePattern,
  NotionPattern,
  SymbolPattern,
  PredicatePatternComp(..),
  NotionPatternComp(..),
  SymbolPatternComp(..)
) where

import Data.Text (Text)

type PredicatePattern = [PredicatePatternComp]

type NotionPattern = [NotionPatternComp]

type SymbolPattern = [SymbolPatternComp]

data PredicatePatternComp
  = PredWord [Text]
  | PredVar
  deriving (Eq, Ord)

data NotionPatternComp
  = NotionWord [Text]
  | NotionVar
  | NotionName
  deriving (Eq, Ord)

data SymbolPatternComp
  = SymbSymbol Text
  | SymbVar
  deriving (Eq, Ord)

