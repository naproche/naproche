module SAD.Data.Pattern where

import Data.Text (Text)
import qualified Data.Text as Text

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
