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

-- | One or more alphanumeric ASCII characters
asciiLexeme :: forall state. Lexer state Text
asciiLexeme = Text.pack <$> some (satisfy isAsciiAlphaNum)

-- | A single ASCII symbol
asciiSymbol :: forall state. Lexer state Text
asciiSymbol = Text.singleton <$> satisfy isAsciiSymbol

-- | A single ASCII character
asciiChar :: forall state. Lexer state Text
asciiChar = Text.singleton <$> satisfy Char.isAscii


-- | One or more alphanumeric ASCII characters such that the result does not
-- match a given list of exceptions
asciiLexemeExcept :: forall state. [String] -> Lexer state Text
asciiLexemeExcept exceptions = do
  result <- some (satisfy isAsciiAlphaNum)
  if result `elem` exceptions
    then empty
    else return $ Text.pack result

-- | A single ASCII symbol that does not match a given list of exceptions
asciiSymbolExcept :: forall state. [Char] -> Lexer state Text
asciiSymbolExcept exceptions = do
  result <- satisfy isAsciiSymbol
  if result `elem` exceptions
    then empty
    else return $ Text.singleton result

-- | A single ASCII character that does not match a given list of exceptions
asciiCharExcept :: forall state. [Char] -> Lexer state Text
asciiCharExcept exceptions = do
  result <- satisfy Char.isAscii
  if result `elem` exceptions
    then empty
    else return $ Text.singleton result


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
