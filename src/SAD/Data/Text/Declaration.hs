module SAD.Data.Text.Declaration (Declaration(..), Serial) where

import SAD.Core.SourcePos

type Serial = Int

data Declaration = Decl {
  name :: String,
  position :: SourcePos,
  serial :: Serial
}