module SAD.Data.Text.Declaration (
  Declaration(..), Serial,
  nonText, nonParser
  ) where

import SAD.Core.SourcePos

type Serial = Int

data Declaration = Decl {
  name :: String,
  position :: SourcePos,
  serial :: Serial
}

{- a declaration that has no representation in the input text -}
nonText :: String -> Declaration
nonText v = Decl v noPos (-1)

{- a declaration that has a representation in the input text but has not been
generated during parsing -}
nonParser :: (String, SourcePos) -> Declaration
nonParser (nm, pos) = Decl nm pos (-1)