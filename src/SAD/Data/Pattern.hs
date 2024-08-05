-- |
-- Module      : SAD.Data.Pattern
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


module SAD.Data.Pattern where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

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
