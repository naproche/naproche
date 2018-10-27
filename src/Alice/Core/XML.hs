{-
Authors: Makarius Wenzel (2018)

Support for XML (see Isabelle/src/Pure/PIDE/xml.ML).
-}

module Alice.Core.XML (Attributes, Markup, Body, Tree(..)) where

type Attributes = [(String, String)]
type Markup = (String, Attributes)
type Body = [Tree]
data Tree = Elem Markup Body | Text String
