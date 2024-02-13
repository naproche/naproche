-- |
-- Author: Marcel Schütz (2024)
--
-- Lexer primitives.


module SAD.Lexer.Primitives where


-- * Character Sets

isValidChar :: Char -> Bool
isValidChar c =
     isLetter c
  || isDigit c
  || isSymbol c
  || isSpace c

isInvalidChar :: Char -> Bool
isInvalidChar c = not (isValidChar c)

isLetter :: Char -> Bool
isLetter c =
     between c 'a' 'z'
  || between c 'A' 'Z'

isDigit :: Char -> Bool
isDigit c = between c '0' '9'

isSymbol :: Char -> Bool
isSymbol c =
     between c '\x21' '\x2f'
  || between c '\x3a' '\x40'
  || between c '\x5b' '\x60'
  || between c '\x7b' '\x7e'

isSpace :: Char -> Bool
isSpace c = c `elem` ['\x0a', '\x20']

isAlphaNum :: Char -> Bool
isAlphaNum c = isLetter c || isDigit c


-- * Helpers

between :: Ord a => a -> a -> a -> Bool
between x a b = a <= x && x <= b
