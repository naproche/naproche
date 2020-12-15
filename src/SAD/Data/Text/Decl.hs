{-
Authors: Steffen Frerix (2018)

Variable declarations.
-}

module SAD.Data.Text.Decl (
  Decl(..), Serial,
  newDecl, positionedDecl
  ) where

import PIDE.SourcePos
import SAD.Data.VarName

-- | >0, with 0 as undefined
type Serial = Int

-- | A variable declaration.
data Decl = Decl {
  declName :: VarName,
  declPosition :: SourcePos,
  declSerial :: Serial
} deriving (Eq, Ord, Show)

{- a declaration that has no representation in the input text -}
newDecl :: VarName -> Decl
newDecl v = Decl v noSourcePos 0

{- a declaration that has a representation in the input text but has not been
generated during parsing -}
positionedDecl :: PosVar -> Decl
positionedDecl (PosVar nm pos) = Decl nm pos 0
