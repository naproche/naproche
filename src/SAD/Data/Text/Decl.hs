{-
Authors: Steffen Frerix (2018)

Variable declarations.
-}

module SAD.Data.Text.Decl (
  Decl(..), Serial,
  nonText, nonParser
  ) where

import SAD.Core.SourcePos

type Serial = Int

data Decl = Decl {
  name :: String,
  position :: SourcePos,
  serial :: Serial
}

{- a declaration that has no representation in the input text -}
nonText :: String -> Decl
nonText v = Decl v noPos 0

{- a declaration that has a representation in the input text but has not been
generated during parsing -}
nonParser :: (String, SourcePos) -> Decl
nonParser (nm, pos) = Decl nm pos 0