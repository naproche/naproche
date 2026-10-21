-- |
-- Module      : SAD.Data.Pattern
-- Description : TODO
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
module SAD.Data.Pattern where

import Data.Text (Text)
import Data.Text qualified as Text

numHoles :: [Pattern] -> Int
numHoles ps = length (filter (==Vr) ps)

data Pattern
  = Word [Text]
  | Symbol Text
  | Vr
  | NamePattern
  deriving (Eq, Ord, Show)

wordPattern :: Text -> Pattern
wordPattern = Word . Text.words
