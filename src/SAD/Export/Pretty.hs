{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Export.Pretty
-- Description : Presenting objects as human-readable text.
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
module SAD.Export.Pretty (
  Pretty(..)
) where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)

import Isabelle.Bytes (Bytes)
import Isabelle.Library (commas, make_bytes, quote)

class Pretty a where
  pretty_print :: a -> Bytes

instance Pretty Text where
  pretty_print = quote . make_bytes

instance Pretty a => Pretty [a] where
  pretty_print as = "[" <> commas (map pretty_print as) <> "]"

instance (Pretty a, Pretty b) => Pretty (a, b) where
  pretty_print (a, b) = "(" <> pretty_print a <> ", " <> pretty_print b <> ")"

instance Pretty a => Pretty (Set a) where
  pretty_print as = "{" <> commas (Set.toList $ Set.map pretty_print as) <> "}"
