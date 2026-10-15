-- |
-- Module      : SAD.Helpers
-- Copyright   : (c) 2019, Adrian De Lon,
--               (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- Helper functions.


module SAD.Helpers (
  isAsciiSymbol,
  isAsciiDigit,
  isAsciiLetter,
  isAsciiAlphaNum,
  isAsciiPeriod,
) where

import Data.Char qualified as Char


-- * Character Categories

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

