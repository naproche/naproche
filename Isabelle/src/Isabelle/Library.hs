{- generated by Isabelle -}

{-  Title:      Isabelle/Library.hs
    Author:     Makarius
    LICENSE:    BSD 3-clause (Isabelle)

Basic library of Isabelle idioms.

See "$ISABELLE_HOME/src/Pure/General/basics.ML"
and "$ISABELLE_HOME/src/Pure/library.ML".
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module Isabelle.Library (
  (|>), (|->), (#>), (#->),

  fold, fold_rev, fold_map, single, the_single, singletonM,
  map_index, get_index, separate,

  StringLike, STRING (..), TEXT (..), BYTES (..),
  show_bytes, show_text,

  proper_string, enclose, quote, space_implode, implode_space, commas, commas_quote,
  cat_lines, space_explode, split_lines, trim_line, trim_split_lines,

  getenv, getenv_strict)
where

import System.Environment (lookupEnv)
import Data.Maybe (fromMaybe)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Text.Lazy as Lazy
import Data.String (IsString)
import qualified Data.List.Split as Split
import qualified Isabelle.Symbol as Symbol
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.UTF8 as UTF8


{- functions -}

(|>) :: a -> (a -> b) -> b
x |> f = f x

(|->) :: (a, b) -> (a -> b -> c) -> c
(x, y) |-> f = f x y

(#>) :: (a -> b) -> (b -> c) -> a -> c
(f #> g) x = x |> f |> g

(#->) :: (a -> (c, b)) -> (c -> b -> d) -> a -> d
(f #-> g) x  = x |> f |-> g


{- lists -}

fold :: (a -> b -> b) -> [a] -> b -> b
fold _ [] y = y
fold f (x : xs) y = fold f xs (f x y)

fold_rev :: (a -> b -> b) -> [a] -> b -> b
fold_rev _ [] y = y
fold_rev f (x : xs) y = f x (fold_rev f xs y)

fold_map :: (a -> b -> (c, b)) -> [a] -> b -> ([c], b)
fold_map _ [] y = ([], y)
fold_map f (x : xs) y =
  let
    (x', y') = f x y
    (xs', y'') = fold_map f xs y'
  in (x' : xs', y'')

single :: a -> [a]
single x = [x]

the_single :: [a] -> a
the_single [x] = x
the_single _ = undefined

singletonM :: Monad m => ([a] -> m [b]) -> a -> m b
singletonM f x = the_single <$> f [x]

map_index :: ((Int, a) -> b) -> [a] -> [b]
map_index f = map_aux 0
  where
    map_aux _ [] = []
    map_aux i (x : xs) = f (i, x) : map_aux (i + 1) xs

get_index :: (a -> Maybe b) -> [a] -> Maybe (Int, b)
get_index f = get_aux 0
  where
    get_aux _ [] = Nothing
    get_aux i (x : xs) =
      case f x of
        Nothing -> get_aux (i + 1) xs
        Just y -> Just (i, y)

separate :: a -> [a] -> [a]
separate s (x : xs@(_ : _)) = x : s : separate s xs
separate _ xs = xs;


{- string-like interfaces -}

class (IsString a, Monoid a, Eq a, Ord a) => StringLike a where
  space_explode :: Char -> a -> [a]
  trim_line :: a -> a

gen_trim_line :: Int -> (Int -> Char) -> (Int -> a -> a) -> a -> a
gen_trim_line n at trim s =
  if n >= 2 && at (n - 2) == '\r' && at (n - 1) == '\n' then trim (n - 2) s
  else if n >= 1 && Symbol.is_ascii_line_terminator (at (n - 1)) then trim (n - 1) s
  else s

instance StringLike String where
  space_explode :: Char -> String -> [String]
  space_explode c = Split.split (Split.dropDelims (Split.whenElt (== c)))
  trim_line :: String -> String
  trim_line s = gen_trim_line (length s) (s !!) take s

instance StringLike Text where
  space_explode :: Char -> Text -> [Text]
  space_explode c str =
    if Text.null str then []
    else if Text.all (/= c) str then [str]
    else map Text.pack $ space_explode c $ Text.unpack str
  trim_line :: Text -> Text
  trim_line s = gen_trim_line (Text.length s) (Text.index s) Text.take s

instance StringLike Lazy.Text where
  space_explode :: Char -> Lazy.Text -> [Lazy.Text]
  space_explode c str =
    if Lazy.null str then []
    else if Lazy.all (/= c) str then [str]
    else map Lazy.pack $ space_explode c $ Lazy.unpack str
  trim_line :: Lazy.Text -> Lazy.Text
  trim_line = Lazy.fromStrict . trim_line . Lazy.toStrict

instance StringLike Bytes where
  space_explode :: Char -> Bytes -> [Bytes]
  space_explode c str =
    if Bytes.null str then []
    else if Bytes.all_char (/= c) str then [str]
    else
      explode (Bytes.unpack str)
      where
        explode rest =
          case span (/= (Bytes.byte c)) rest of
            (_, []) -> [Bytes.pack rest]
            (prfx, _ : rest') -> Bytes.pack prfx : explode rest'
  trim_line :: Bytes -> Bytes
  trim_line s = gen_trim_line (Bytes.length s) (Bytes.char . Bytes.index s) Bytes.take s

class StringLike a => STRING a where make_string :: a -> String
instance STRING String where make_string = id
instance STRING Text where make_string = Text.unpack
instance STRING Lazy.Text where make_string = Lazy.unpack
instance STRING Bytes where make_string = UTF8.decode

class StringLike a => TEXT a where make_text :: a -> Text
instance TEXT String where make_text = Text.pack
instance TEXT Text where make_text = id
instance TEXT Lazy.Text where make_text = Lazy.toStrict
instance TEXT Bytes where make_text = UTF8.decode

class StringLike a => BYTES a where make_bytes :: a -> Bytes
instance BYTES String where make_bytes = UTF8.encode
instance BYTES Text where make_bytes = UTF8.encode
instance BYTES Lazy.Text where make_bytes = UTF8.encode . Lazy.toStrict
instance BYTES Bytes where make_bytes = id

show_bytes :: Show a => a -> Bytes
show_bytes = make_bytes . show

show_text :: Show a => a -> Text
show_text = make_text . show


{- strings -}

proper_string :: StringLike a => a -> Maybe a
proper_string s = if s == "" then Nothing else Just s

enclose :: StringLike a => a -> a -> a -> a
enclose lpar rpar str = lpar <> str <> rpar

quote :: StringLike a => a -> a
quote = enclose "\"" "\""

space_implode :: StringLike a => a -> [a] -> a
space_implode s = mconcat . separate s

implode_space :: StringLike a => [a] -> a
implode_space = space_implode " "

commas, commas_quote :: StringLike a => [a] -> a
commas = space_implode ", "
commas_quote = commas . map quote

split_lines :: StringLike a => a -> [a]
split_lines = space_explode '\n'

cat_lines :: StringLike a => [a] -> a
cat_lines = space_implode "\n"

trim_split_lines :: StringLike a => a -> [a]
trim_split_lines = trim_line #> split_lines #> map trim_line


{- getenv -}

getenv :: Bytes -> IO Bytes
getenv x = do
  y <- lookupEnv (make_string x)
  return $ make_bytes $ fromMaybe "" y

getenv_strict :: Bytes -> IO Bytes
getenv_strict x = do
  y <- getenv x
  if Bytes.null y then
    errorWithoutStackTrace $ make_string ("Undefined Isabelle environment variable: " <> quote x)
  else return y
