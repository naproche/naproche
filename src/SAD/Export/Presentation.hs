{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Export.Presentation
-- Description : Presenting objects as human-readable text.
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
module SAD.Export.Presentation (
  Presentation(..)
) where

import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)

import Isabelle.Library (commas)

class Presentation a where
  present :: a -> Text

instance Presentation a => Presentation [a] where
  present as = "[" <> commas (map present as) <> "]"

instance (Presentation a, Presentation b) => Presentation (a, b) where
  present (a, b) = "(" <> present a <> ", " <> present b <> ")"

instance Presentation a => Presentation (Set a) where
  present as = "{" <> commas (Set.toList $ Set.map present as) <> "}"
