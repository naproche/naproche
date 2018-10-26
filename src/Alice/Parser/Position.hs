{-
Authors: Steffen Frerix (2017 - 2018)

Token source positions.
-}


module Alice.Parser.Position
  ( SourcePos (EOF, sourceFile, sourceLine, sourceColumn, sourceOffset),
    SourceName,
    noPos,
    namePos,
    initialPos,
    advancePos,
    advancesPos )
  where

import Data.List

type SourceName = String

data SourcePos =
  SourcePos {
    sourceFile :: SourceName,
    sourceLine :: Int,
    sourceColumn :: Int,
    sourceOffset :: Int }
  | EOF
  deriving (Eq, Ord)


noPos :: SourcePos
noPos = SourcePos "" 0 0 0

namePos :: SourceName -> SourcePos
namePos name = SourcePos name 0 0 0

initialPos :: SourceName -> SourcePos
initialPos name = SourcePos name 1 1 1

advanceLine line c = if line <= 0 || c /= '\n' then line else line + 1
advanceColumn column c = if column <= 0 then column else if c == '\n' then 1 else column + 1
advanceOffset offset c = if offset <= 0 then offset else offset + 1

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
  show (SourcePos name line column offset) =
    if null showName then showDetails
    else if null showDetails then showName
    else showName ++ " " ++ showDetails
    where
      detail a i = if i <= 0 then "" else a ++ " " ++ show i
      details = [detail "line" line, detail "column" column, detail "offset" offset]
      showDetails =
        case filter (not . null) details of
          [] -> ""
          ds -> "(" ++ intercalate "," ds ++ ")"
      showName = if null name then "" else "\"" ++ name ++ "\""
