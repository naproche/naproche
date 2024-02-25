-- |
-- Author: Marcel Schütz (2024)
--
-- Character sets for lexing.


module SAD.Lexer.Char where


-- * Character Sets

isValidChar :: Char -> Bool
isValidChar c =
     isLetter c
  || isDigit c
  || isSymbol c
  || isSpace c

isCommentChar :: Char -> Bool
isCommentChar c =
     isLetter c
  || isDigit c
  || isSymbol c
  || isHorizontalSpace c

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
isSpace c =
     isHorizontalSpace c
  || isVerticalSpace c

isHorizontalSpace :: Char -> Bool
isHorizontalSpace c = c == '\x20'

isVerticalSpace :: Char -> Bool
isVerticalSpace c = c == '\x0a'

isAlphaNum :: Char -> Bool
isAlphaNum c = isLetter c || isDigit c


-- * Helpers

between :: Ord a => a -> a -> a -> Bool
between x a b = a <= x && x <= b
