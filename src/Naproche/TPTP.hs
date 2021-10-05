{-
Authors: Makarius Wenzel (2021)

Support for TPTP syntax.

See also http://www.tptp.org/TPTP/SyntaxBNF.html
-}

{-# LANGUAGE OverloadedStrings #-}

module Naproche.TPTP (
  is_lower_word, is_upper_word, atomic_word
)
where

import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)


{- predicates -}

is_numeric, is_lower_alpha, is_upper_alpha, is_alpha_numeric :: Char -> Bool
is_numeric c = '0' <= c && c <= '9'
is_lower_alpha c = 'a' <= c && c <= 'z'
is_upper_alpha c = 'A' <= c && c <= 'Z'
is_alpha_numeric c = is_lower_alpha c || is_upper_alpha c || is_numeric c || c == '_'

is_word :: (Char -> Bool) -> Bytes -> Bool
is_word is_head s =
  not (Bytes.null s) && is_head (Bytes.char (Bytes.head s)) &&
  Bytes.all_char is_alpha_numeric s

is_lower_word, is_upper_word :: Bytes -> Bool
is_lower_word = is_word is_lower_alpha
is_upper_word = is_word is_upper_alpha


{- make atomic words -}

atomic_word :: Bytes -> Bytes
atomic_word s
  | is_lower_word s = s
  | Bytes.any esc s = Bytes.concat ([q] ++ map escape (Bytes.unpack s) ++ [q])
  | otherwise = q <> s <> q
  where
    single_quote = Bytes.byte '\''
    backslash = Bytes.byte '\\'
    q = Bytes.singleton single_quote
    esc b = b == single_quote || b == backslash
    escape b = if esc b then Bytes.pack [backslash, b] else Bytes.singleton b
