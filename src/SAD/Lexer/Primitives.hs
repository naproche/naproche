-- |
-- Author: Marcel Schütz (2024)
--
-- Lexer primitives.


module SAD.Lexer.Primitives where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.Char qualified as Char
import Text.Megaparsec hiding (between)

import SAD.Lexer.Base


-- * Lexers

-- | One or more alphanumeric ASCII character
asciiAlphaNum :: forall state. Lexer state Text
asciiAlphaNum = Text.pack <$> some (satisfy isAsciiAlphaNum)

-- | A single ASCII symbol
asciiSymbol :: forall state. Lexer state Text
asciiSymbol = Text.singleton <$> satisfy isAsciiSymbol

asciiChar :: forall state. Lexer state Text
asciiChar = Text.singleton <$> satisfy Char.isAscii


-- * Character Sets

isAsciiSymbol :: Char -> Bool
isAsciiSymbol c =
     between c '\x21' '\x2f'
  || between c '\x3a' '\x40'
  || between c '\x5b' '\x60'
  || between c '\x7b' '\x7e'

isAsciiAlphaNum :: Char -> Bool
isAsciiAlphaNum c = Char.isAscii c && Char.isAlphaNum c


-- * Helpers

between :: Ord a => a -> a -> a -> Bool
between x a b = a <= x && x <= b
