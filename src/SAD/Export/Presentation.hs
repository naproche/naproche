-- |
-- Module      : SAD.Export.Presentation
-- Description : Presenting objects as human-readable text.
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
module SAD.Export.Presentation (
  Presentation(..)
) where

import Data.Text (Text)


class Presentation a where
  present :: a -> Text
