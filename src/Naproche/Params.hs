{-
Authors: Makarius Wenzel (2022)

Parameters of various types, represented as plain bytes.
-}

{-# LANGUAGE OverloadedStrings #-}

module Naproche.Params (
  T, empty, description,
  bool, int, real, string, strings,
  set_bool, set_int, set_real, set_string, set_strings, reset,
  init_bool, init_int, init_real, init_string, init_strings
)
where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Value as Value
import Isabelle.Library


{- compact string list -}

decode_strings :: Bytes -> [Bytes]
decode_strings = space_explode '\0'

encode_strings :: [Bytes] -> Bytes
encode_strings = space_implode "\0" . map make_bytes


{- representation -}

boolT :: Bytes
boolT = "bool"

intT :: Bytes
intT = "int"

realT :: Bytes
realT = "real"

stringT :: Bytes
stringT = "string"

stringsT :: Bytes
stringsT = "strings"

data Param = Param {
  _typ :: Bytes,
  _name :: Bytes,
  _descr :: Bytes,
  _default :: Bytes,
  _value :: Bytes }

instance Show Param
  where show Param{_name = a, _typ = b} = make_string (a <> " : " <> b)


newtype T = Params (Map Bytes Param)

instance Show T
  where show (Params ps) = show $ map snd $ Map.toList ps

empty :: T
empty = Params Map.empty


{- check -}

check_name :: T -> Bytes -> Param
check_name (Params ps) name =
  case Map.lookup name ps of
    Just param -> param
    _ -> error (make_string ("Unknown parameter name " <> quote name))

check_type :: T -> Bytes -> Bytes -> Param
check_type params name typ =
  let
    param = check_name params name
    t = _typ param
  in
    if t == typ then param
    else error (make_string ("Ill-typed parameter " <> quote name <> " : " <> t <> " vs. " <> typ))


{- description -}

description :: T -> Bytes -> Bytes
description params name = _descr $ check_name params name


{- get value -}

get :: Bytes -> (Bytes -> Maybe a) -> T -> Bytes -> a
get typ parse params name =
  let param = check_type params name typ in
    case parse (_value param) of
      Just x -> x
      Nothing ->
        error (make_string ("Malformed value for parameter " <> quote name <>
          " : " <> typ <> " =\n" <> quote (_value param)))

bool :: T -> Bytes -> Bool
bool = get boolT Value.parse_bool

int :: T -> Bytes -> Int
int = get intT Value.parse_int

real :: T -> Bytes -> Double
real = get realT Value.parse_real

string :: T -> Bytes -> Bytes
string = get stringT Just

strings :: T -> Bytes -> [Bytes]
strings = get stringsT (Just . decode_strings)


{- set value -}

set :: Bytes -> (a -> Bytes) -> Bytes -> a -> T -> T
set typ print name x params =
  let
    param' = (check_type params name typ) { _value = print x }
    Params ps = params
  in Params (Map.insert name param' ps)

set_bool :: Bytes -> Bool -> T -> T
set_bool = set boolT Value.print_bool

set_int :: Bytes -> Int -> T -> T
set_int = set intT Value.print_int

set_real :: Bytes -> Double -> T -> T
set_real = set realT Value.print_real

set_string :: Bytes -> Bytes -> T -> T
set_string = set stringT make_bytes

set_strings :: Bytes -> [Bytes] -> T -> T
set_strings = set stringsT encode_strings


{- reset value -}

reset :: Bytes -> T -> T
reset name params =
  let
    param = check_name params name
    param' = param { _value = _default param }
    Params ps = params
  in Params (Map.insert name param' ps)


{- init parameters -}

init_param :: Bytes -> Bytes -> Bytes -> Bytes -> T -> T
init_param typ name descr value (Params ps) =
  if Map.member name ps
  then error (make_string ("Duplicate declaration of parameter " <> quote name))
  else Params (Map.insert name (Param typ name descr value value) ps)

init_bool :: Bytes -> Bytes -> Bool -> T -> T
init_bool name descr = init_param boolT name descr . Value.print_bool

init_int :: Bytes -> Bytes -> Int -> T -> T
init_int name descr = init_param intT name descr . Value.print_int

init_real :: Bytes -> Bytes -> Double -> T -> T
init_real name descr = init_param realT name descr . Value.print_real

init_string :: Bytes -> Bytes -> Bytes -> T -> T
init_string name descr = init_param stringT name descr . make_bytes

init_strings :: Bytes -> Bytes -> [Bytes] -> T -> T
init_strings name descr = init_param stringsT name descr . encode_strings
