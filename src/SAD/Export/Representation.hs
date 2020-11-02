{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.Representation
  ( Representation(..)
  , buildParens
  , buildArgumentsWith
  , commaSeparated
  )where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Functor.Identity
import Data.Functor.Const
import Data.Functor.Product

class Representation a where
  represent :: a -> Text

instance Representation a => Representation (Identity a) where
  represent (Identity a) = represent a

instance Representation a => Representation (Const a b) where
  represent (Const a) = represent a

instance (Representation a, Representation (f a), Representation (g a)) => Representation (Product f g a) where
  represent (Pair f g) = represent (f, g)

instance Representation () where
  represent () = "()"

instance (Representation a, Representation b) => Representation (a, b) where
  represent (a, b) = "(" <> represent a <> ", " <> represent b <> ")"

instance Representation a => Representation [a] where
  represent [] = "[]"
  represent xs = "[" <> Text.intercalate ", " (map represent xs) <> "]"

instance Representation a => Representation (Set a) where
  represent s = if Set.null s then "{}"
    else "{" <> Text.intercalate ", " (map represent (Set.toList s)) <> "}"

instance Representation a => Representation (Maybe a) where
  represent Nothing = "Nothing"
  represent (Just a) = "Just " <> represent a

buildParens :: Text -> Text
buildParens xs = "(" <> xs <> ")"

buildArgumentsWith :: (a -> Text) -> [a] -> Text
buildArgumentsWith _ [] = ""
buildArgumentsWith showTerm ls = buildParens $ commaSeparated showTerm ls

commaSeparated :: (a -> Text) -> [a] -> Text
commaSeparated _ [] = ""
commaSeparated showTerm [t] = showTerm t
commaSeparated showTerm (t:ts) = showTerm t <> "," <> commaSeparated showTerm ts