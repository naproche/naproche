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

  failureMessage,
  failWithMessage,
  exitWithError,

  getNaprocheHome,
  getNaprocheFormalizations,
  getNaprocheMathhub
) where

import Data.Char qualified as Char

import Isabelle.Library (make_bytes, getenv, make_string)


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


-- * Error Messages

failureMessage :: String -> String -> String
failureMessage functionId message = functionId ++ ": " ++ message ++
    " If you see this message, please file an issue at " ++
    " <https://github.com/naproche/naproche/issues>."

failWithMessage :: String -> String -> a
failWithMessage functionId message = error $ failureMessage functionId message

exitWithError :: String -> a
exitWithError message = errorWithoutStackTrace $ "[Error] " ++ message

-- *

-- | Get the path to the naproche directory.
getNaprocheHome :: IO FilePath
getNaprocheHome = make_string <$> getenv (make_bytes "NAPROCHE_HOME")

-- | Get the path to the formalizations directory.
getNaprocheFormalizations :: IO FilePath
getNaprocheFormalizations = make_string <$> getenv (make_bytes "NAPROCHE_FORMALIZATIONS")

-- | Get the path to the formalizations directory.
getNaprocheMathhub :: IO FilePath
getNaprocheMathhub = make_string <$> getenv (make_bytes "NAPROCHE_MATHHUB")
