{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.Pretty
  ( Pretty(..)
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

class Pretty a where
  pretty :: a -> Text

instance Pretty a => Pretty (Identity a) where
  pretty (Identity a) = pretty a

instance Pretty a => Pretty (Const a b) where
  pretty (Const a) = pretty a

instance (Pretty a, Pretty (f a), Pretty (g a)) => Pretty (Product f g a) where
  pretty (Pair f g) = pretty (f, g)

instance Pretty () where
  pretty () = "()"

instance (Pretty a, Pretty b) => Pretty (a, b) where
  pretty (a, b) = "(" <> pretty a <> ", " <> pretty b <> ")"

instance Pretty a => Pretty [a] where
  pretty [] = "[]"
  pretty xs = "[" <> Text.intercalate ", " (map pretty xs) <> "]"

instance Pretty a => Pretty (Set a) where
  pretty s = if Set.null s then "{}"
    else "{" <> Text.intercalate ", " (map pretty (Set.toList s)) <> "}"

instance Pretty a => Pretty (Maybe a) where
  pretty Nothing = "Nothing"
  pretty (Just a) = "Just " <> pretty a

buildParens :: Text -> Text
buildParens xs = "(" <> xs <> ")"

buildArgumentsWith :: (a -> Text) -> [a] -> Text
buildArgumentsWith _ [] = ""
buildArgumentsWith showTerm ls = buildParens $ commaSeparated showTerm ls

commaSeparated :: (a -> Text) -> [a] -> Text
commaSeparated _ [] = ""
commaSeparated showTerm [t] = showTerm t
commaSeparated showTerm (t:ts) = showTerm t <> "," <> commaSeparated showTerm ts