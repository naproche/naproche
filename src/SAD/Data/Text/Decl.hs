-- |
-- Module      : SAD.Data.Text.Decl
-- Copyright   : (c) 2018, Steffen Frerix
-- License     : GPL-3
--
-- Variable declarations.


module SAD.Data.Text.Decl (
  Decl(..),
  Serial,
  newDecl,
  positionedDecl
) where

import SAD.Data.VarName

import Isabelle.Position qualified as Position


-- | >0, with 0 as undefined
type Serial = Int

-- | A variable declaration.
data Decl = Decl {
  declName :: VariableName,
  declPosition :: Position.T,
  declSerial :: Serial
} deriving (Eq, Ord)

instance Show Decl where
  show = show . declName

{- a declaration that has no representation in the input text -}
newDecl :: VariableName -> Decl
newDecl v = Decl v Position.none 0

{- a declaration that has a representation in the input text but has not been
generated during parsing -}
positionedDecl :: PosVar -> Decl
positionedDecl (PosVar nm pos) = Decl nm pos 0
