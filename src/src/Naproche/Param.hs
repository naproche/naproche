{-
Authors: Makarius Wenzel (2022)

Typed parameters, stored via plain bytes.
-}

{-# LANGUAGE OverloadedStrings #-}

module Naproche.Param (
  print_flag, parse_flag,
  T, name, unnamed, description, description_default,
  bytes, bool, flag, nat, int, real,
  Env, empty, parse, get, put
)
where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Value as Value
import Isabelle.Library


{- flags -}

print_flag :: Bool -> Bytes
print_flag True = "on" 
print_flag False = "off"

parse_flag :: Bytes -> Maybe Bool
parse_flag "on" = Just True
parse_flag "off" = Just False
parse_flag "yes" = Just True
parse_flag "no" = Just False
parse_flag _ = Nothing


{- typed parameters -}

data T a = Param {
  _print :: a -> Bytes,
  _parse :: Bytes -> Maybe a,
  _name :: Bytes,
  _descr :: Bytes,
  _default :: a }

name :: T a -> Bytes
name Param{_name = a} = a

unnamed :: T a -> T a
unnamed p = p { _name = ""}

description :: T a -> Bytes
description Param{_descr = a} = a

description_default :: T a -> Bytes
description_default Param{_descr = a, _print = print, _default = x} =
  a <> " (default: " <> print x <> ")"

instance Eq (T a) where p == p' = name p == name p'
instance Ord (T a) where compare p p' = compare (name p) (name p')
instance Show (T a) where show = make_string . name

bytes :: Bytes -> Bytes -> Bytes -> T Bytes
bytes = Param id Just
  
bool :: Bytes -> Bytes -> Bool -> T Bool
bool = Param Value.print_bool Value.parse_bool

flag :: Bytes -> Bytes -> Bool -> T Bool
flag = Param print_flag parse_flag

nat :: Bytes -> Bytes -> Int -> T Int
nat = Param Value.print_int Value.parse_nat

int :: Bytes -> Bytes -> Int -> T Int
int = Param Value.print_int Value.parse_int

real :: Bytes -> Bytes -> Double -> T Double
real = Param Value.print_real Value.parse_real


{- untyped environment -}

newtype Env = Env (Map Bytes Bytes)

instance Show Env
  where show (Env ps) = show $ map fst $ Map.toList ps

empty :: Env
empty = Env Map.empty

parse :: T a -> Bytes -> a
parse Param{_name = a, _parse = parse} s =
  case parse s of
    Nothing ->
      error (make_string ("Malformed value for parameter " <> quote a <> " =\n  " <> quote s))
    Just x -> x

get :: T a -> Env -> a
get p@Param{_name = a, _default = x} (Env ps) =
  maybe x (parse p) (Map.lookup a ps)

put :: T a -> a -> Env -> Env
put Param{_name = a, _print = print} x (Env ps) =
  Env (Map.insert a (print x) ps)
