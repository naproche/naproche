{-
Authors: Makarius Wenzel (2022)

Typed parameters, stored via plain bytes.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}

module Naproche.Param (
  T, name, description, bool, int, real, string, strings,
  Env, empty, declare, get, put, input, restore
)
where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Value as Value
import Isabelle.Library


{- typed parameters -}

data T a = Param {
  _print :: a -> Bytes,
  _parse :: Bytes -> Maybe a,
  _name :: Bytes,
  _description :: Bytes,
  _default :: a }

name :: T a -> Bytes
name Param{_name = a} = a

description :: T a -> Bytes
description Param{_description = a} = a

instance Show (T a)
  where show = make_string . name

bool :: Bytes -> Bytes -> Bool -> T Bool
bool = Param Value.print_bool Value.parse_bool

int :: Bytes -> Bytes -> Int -> T Int
int = Param Value.print_int Value.parse_int

real :: Bytes -> Bytes -> Double -> T Double
real = Param Value.print_real Value.parse_real

string :: Bytes -> Bytes -> Bytes -> T Bytes
string = Param id Just

strings :: Bytes -> Bytes -> [Bytes] -> T [Bytes]
strings = Param (space_implode "\0") (Just . space_explode '\0')


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

error_malformed :: Bytes -> Bytes -> a
error_malformed a s =
  error (make_string ("Malformed value for parameter " <> quote a <> " =\n  " <> quote s))

get :: T a -> Env -> a
get p@Param{_name = a, _parse = parse} env =
  let s = check p env in
    case parse s of
      Nothing -> error_malformed a s
      Just x -> x

put :: T a -> a -> Env -> Env
put p@Param{_name = a, _print = print} x env =
  let !_ = check p env; Env ps = env
  in Env (Map.insert a (print x) ps)

input :: T a -> Bytes -> Env -> Env
input p@Param{_name = a, _parse = parse} s env =
  case parse s of
    Nothing -> error_malformed a s
    Just x -> put p x env

restore :: T a -> Env -> Env
restore p@Param{_default = x} = put p x
