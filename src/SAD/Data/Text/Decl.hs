{-
Authors: Steffen Frerix (2018)

Variable declarations.
-}

module SAD.Data.Text.Decl (
  Decl(..), Serial,
  nonText, nonParser
  ) where

import SAD.Core.SourcePos
import SAD.Data.VarName

-- | >0, with 0 as undefined
type Serial = Int

-- | A variable declaration.
data Decl = Decl {
  name :: VariableName,
  position :: SourcePos,
  serial :: Serial
} deriving (Eq, Ord)

{- a declaration that has no representation in the input text -}
nonText :: VariableName -> Decl
nonText v = Decl v noSourcePos 0

{- a declaration that has a representation in the input text but has not been
generated during parsing -}
nonParser :: (VariableName, SourcePos) -> Decl
nonParser (nm, pos) = Decl nm pos 0
