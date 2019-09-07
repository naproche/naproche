{-
Authors: Steffen Frerix (2018)

Variable declarations.
-}

module SAD.Data.Text.Decl (
  Decl(..), Serial,
  nonText, nonParser
  ) where

import SAD.Core.SourcePos

-- | >0, with 0 as undefined
type Serial = Int

-- | A variable declaration.
data Decl = Decl {
  name :: String,
  position :: SourcePos,
  serial :: Serial
}

{- a declaration that has no representation in the input text -}
nonText :: String -> Decl
nonText v = Decl v noSourcePos 0

{- a declaration that has a representation in the input text but has not been
generated during parsing -}
nonParser :: (String, SourcePos) -> Decl
nonParser (nm, pos) = Decl nm pos 0