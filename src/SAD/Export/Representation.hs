-- |
-- Module      : SAD.Export.Representation
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


module SAD.Export.Representation (
  Representation(..)
) where

import Data.Text (Text)


class Representation a where
  represent :: a -> Text
