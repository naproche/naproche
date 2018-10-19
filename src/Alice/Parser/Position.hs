{-
Authors: Steffen Frerix (2017 - 2018)

Token source positions.
-}


module Alice.Parser.Position
  ( SourcePos (EOF, sourceFile, sourceLine, sourceColumn, sourceOffset),
    SourceName,
    initialPos,
    advancePos,
    advancesPos )
  where

type SourceName = String
type Line = Int
type Column = Int
type Offset = Int

data SourcePos = SourcePos { sourceFile   :: SourceName,
                             sourceLine   :: Line,
                             sourceColumn :: Column,
                             sourceOffset :: Offset }
               | EOF
               deriving (Eq, Ord)


initialPos :: SourceName -> SourcePos
initialPos name = SourcePos name 1 1 1

advanceLine line c = if c == '\n' then line + 1 else line
advanceColumn column c = if c == '\n' then 1 else column + 1
advanceOffset offset c = offset + 1

advancePos :: SourcePos -> Char -> SourcePos
advancePos (SourcePos name line column offset) c =
  SourcePos name
    (advanceLine line c)
    (advanceColumn column c)
    (advanceOffset offset c)

advancesPos :: SourcePos -> String -> SourcePos
advancesPos (SourcePos name line column offset) s =
  SourcePos name
    (foldl advanceLine line s)
    (foldl advanceColumn column s)
    (foldl advanceOffset offset s)


instance Show SourcePos where
  show EOF = "(end of input)"
  show (SourcePos name line column offset)
    | null name = showLineColumn
    | otherwise = "\"" ++ name ++ "\" " ++ showLineColumn
    where
      showLineColumn =
        "(line " ++ show line ++
        ", column " ++ show column ++
        ", offset " ++ show offset ++
        ")"
