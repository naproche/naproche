-- |
-- Module      : SAD.Data.Text.Decl
-- Description : Variable declarations.
-- Copyright   : (c) 2018, Steffen Frerix
-- License     : GPL-3
module SAD.Data.Text.Decl (
  Decl(..),
  Serial,
  newDecl
) where

import Isabelle.Position qualified as Position

import SAD.Data.VarName


-- | >0, with 0 as undefined
type Serial = Int

-- | A variable declaration.
data Decl = Decl {
  declName :: VariableName,
  declPosition :: Position.T,
  declSerial :: Serial
} deriving (Eq, Ord)

{- a declaration that has no representation in the input text -}
newDecl :: VariableName -> Decl
newDecl v = Decl v Position.none 0
