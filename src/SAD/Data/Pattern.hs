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

-- | DANGER: Not symmetric on `Word`
samePat :: [Pattern] -> [Pattern] -> Bool
samePat [] [] = True
samePat (x:xs) (y:ys) = samePat1 x y && samePat xs ys
  where
    samePat1 (Word ls) (Word rs) = all (`elem` rs) ls
    samePat1 Vr Vr = True
    samePat1 NamePattern NamePattern = True
    samePat1 (Symbol s) (Symbol t) = s == t
    samePat1 _ _ = False
samePat _ _ = False
