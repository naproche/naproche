-- |
-- Module      : SAD.Parser.Char
-- Copyright   : (c) 2026 Marcel Schütz
-- License     : GPL-3
--
-- Character Categories.
module SAD.Parser.Char where

import Data.Char qualified as Char


isAsciiSymbol :: Char -> Bool
isAsciiSymbol c =
     ('\x0021' <= c && c <= '\x002F')
  || ('\x003A' <= c && c <= '\x0040')
  || ('\x005B' <= c && c <= '\x0060')
  || ('\x007B' <= c && c <= '\x007E')

isAsciiDigit :: Char -> Bool
isAsciiDigit = Char.isDigit

isAsciiLetter :: Char -> Bool
isAsciiLetter c = Char.isAsciiUpper c || Char.isAsciiLower c

isAsciiAlphaNum :: Char -> Bool
isAsciiAlphaNum c = isAsciiLetter c || isAsciiDigit c

isAsciiPeriod :: Char -> Bool
isAsciiPeriod c = c == '\x002E'

