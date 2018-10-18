{-
Authors: Steffen Frerix (2017 - 2018)

Token source positions.
-}


module Alice.Parser.Position
  ( SourcePos (EOF, sourceFile, sourceLine, sourceColumn),
    SourceName,
    newPos,
    initialPos )
  where

type SourceName = String
type Line = Int
type Column = Int

data SourcePos = SourcePos { sourceFile   :: SourceName,
                             sourceLine   :: Line,
                             sourceColumn :: Column}
               | EOF
               deriving (Eq, Ord)


newPos :: SourceName -> Line -> Column -> SourcePos
newPos name line column = SourcePos name line column

initialPos :: SourceName -> SourcePos
initialPos name = newPos name 1 1

instance Show SourcePos where
  show EOF = "(end of input)"
  show (SourcePos name line column)
    | null name = showLineColumn
    | otherwise = "\"" ++ name ++ "\" " ++ showLineColumn
    where
      showLineColumn    = "(line " ++ show line ++
                          ", column " ++ show column ++
                          ")"
