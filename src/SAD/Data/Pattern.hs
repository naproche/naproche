-- |
-- Authors: Anton Lorenzen (2019)
--
-- TODO: Add description.


module SAD.Data.Pattern where

import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

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
