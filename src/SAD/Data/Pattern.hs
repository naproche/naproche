-- |
-- Module      : SAD.Data.Pattern
-- Description : TODO
-- Copyright   : (c) 2019, Anton Lorenzen
--               (c) 2026, Marcel Schütz
-- License     : GPL-3
module SAD.Data.Pattern (
  Pattern,
  PatternComp(..)
) where

import Data.Text (Text)

type Pattern = [PatternComp]

data PatternComp
  = Word [Text]
  | Symbol Text
  | Vr
  | Nm
  deriving (Eq, Ord, Show)

