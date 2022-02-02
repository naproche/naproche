{-
Authors: Makarius Wenzel (2022)

Typed parameters, stored via plain bytes.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

module Naproche.Param (
  print_flag, parse_flag,
  T, name, description, description_default,
  bool, flag, nat, int, real, string,
  Env, empty, declare, parse, get, put, input, restore
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

instance Eq (T a) where p == p' = name p == name p'
instance Ord (T a) where compare p p' = compare (name p) (name p')

description :: T a -> Bytes
description Param{_descr = a} = a

description_default :: T a -> Bytes
description_default Param{_descr = a, _print = print, _default = x} =
  a <> " (default: " <> print x <> ")"

instance Show (T a)
  where show = make_string . name

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

string :: Bytes -> Bytes -> Bytes -> T Bytes
string = Param id Just


{- untyped environment -}

newtype Env = Env (Map Bytes Bytes)

instance Show Env
  where show (Env ps) = show $ map fst $ Map.toList ps

empty :: Env
empty = Env Map.empty

declare :: T a -> Env -> Env
declare Param{_name = a, _print = print, _default = x} env =
  let Env ps = env in
    case Map.lookup a ps of
      Nothing -> Env (Map.insert a (print x) ps)
      Just _ -> error (make_string ("Duplicate declaration of parameter " <> quote a))

check :: T a -> Env -> Bytes
check Param{_name = a, _parse = parse} env =
  let Env ps = env in
    case Map.lookup a ps of
      Nothing -> error (make_string ("Unknown parameter " <> quote a))
      Just s -> s

parse :: T a -> Bytes -> a
parse Param{_name = a, _parse = parse} s =
  case parse s of
    Nothing ->
      error (make_string ("Malformed value for parameter " <> quote a <> " =\n  " <> quote s))
    Just x -> x

get :: T a -> Env -> a
get p env = parse p $ check p env

put :: T a -> a -> Env -> Env
put p@Param{_name = a, _print = print} x env =
  let !_ = check p env; Env ps = env
  in Env (Map.insert a (print x) ps)

input :: T a -> Bytes -> Env -> Env
input p s = put p $ parse p s

restore :: T a -> Env -> Env
restore p = put p $ _default p
