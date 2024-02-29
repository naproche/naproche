-- |
-- Author: Marcel Schütz (2024)
--
-- Character sets for lexing.


module SAD.Lexer.Char where


-- * Character Sets

isValidChar :: Char -> Bool
isValidChar =
    isLetter
  ∨ isDigit
  ∨ isSymbol
  ∨ isSpace

isVisibleChar :: Char -> Bool
isVisibleChar =
    isLetter
  ∨ isDigit
  ∨ isSymbol

isCommentChar :: Char -> Bool
isCommentChar =
    isLetter
  ∨ isDigit
  ∨ isSymbol
  ∨ isHorizontalSpace

isInvalidChar :: Char -> Bool
isInvalidChar c = not (isValidChar c)

isLetter :: Char -> Bool
isLetter = between 'a' 'z' ∨ between 'A' 'Z'

isDigit :: Char -> Bool
isDigit = between '0' '9'

isSymbol :: Char -> Bool
isSymbol =
    between '\x21' '\x2f'
  ∨ between '\x3a' '\x40'
  ∨ between '\x5b' '\x60'
  ∨ between '\x7b' '\x7e'

isSpace :: Char -> Bool
isSpace = isHorizontalSpace ∨ isVerticalSpace

isHorizontalSpace :: Char -> Bool
isHorizontalSpace c = c == '\x20'

isVerticalSpace :: Char -> Bool
isVerticalSpace c = c == '\x0a'

isAlphaNum :: Char -> Bool
isAlphaNum = isLetter ∨ isDigit


-- * Helpers

infixr ∨
(∨) :: (Char -> Bool) -> (Char -> Bool) -> Char -> Bool
(p ∨ q) c = p c || q c

between :: Char -> Char -> Char -> Bool
between min max x = min <= x && x <= max
