-- |
-- Module      : SAD.Export.Presentation
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- Presenting objects as human-readable text.
module SAD.Export.Presentation (
  Presentation(..)
) where

import Data.Text (Text)


class Presentation a where
  present :: a -> Text
