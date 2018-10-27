{-
Authors: Makarius Wenzel (2018)

Support for YXML (see Isabelle/src/Pure/PIDE/yxml.ML).
-}

module Alice.Core.YXML (showTree, showBody)
where

import Data.Char
import qualified Alice.Core.XML as XML


-- YXML markers

charX, charY :: Char
charX = chr 5
charY = chr 6

x, y, xy, xyx :: String
x = [charX]
y = [charY]
xy = x ++ y
xyx = xy ++ x


-- buffer

type Buffer = [String]

bufferContent :: Buffer -> String
bufferContent = concat . reverse

bufferAttributes :: Buffer -> XML.Attributes -> Buffer
bufferAttributes = foldl (\buf (a, b) -> b : "=" : a : y : buf)

bufferTree :: Buffer -> XML.Tree -> Buffer
bufferTree buf (XML.Elem (name, atts) ts) =
  xyx : foldl bufferTree (x : bufferAttributes (name : xy : buf) atts) ts
bufferTree buf (XML.Text s) = s : buf


-- show

showTree :: XML.Tree -> String
showTree t = bufferContent (bufferTree [] t)

showBody :: XML.Body -> String
showBody ts = bufferContent (foldl bufferTree [] ts)
