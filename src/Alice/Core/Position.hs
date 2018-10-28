{-
Authors: Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Token source positions.
-}


module Alice.Core.Position
  ( SourcePos (EOF, sourceFile, sourceLine, sourceColumn, sourceOffset),
    noPos,
    fileOnlyPos,
    filePos,
    advancePos,
    advancesPos,
    posProperties)
  where

import Data.List

data SourcePos =
  SourcePos {
    sourceFile :: String,
    sourceLine :: Int,
    sourceColumn :: Int,
    sourceOffset :: Int }
  | EOF
  deriving (Eq, Ord)


noPos :: SourcePos
noPos = SourcePos "" 0 0 0

fileOnlyPos :: String -> SourcePos
fileOnlyPos file = SourcePos file 0 0 0

filePos :: String -> SourcePos
filePos file = SourcePos file 1 1 1

advanceLine line c = if line <= 0 || c /= '\n' then line else line + 1
advanceColumn column c = if column <= 0 then column else if c == '\n' then 1 else column + 1
advanceOffset offset c = if offset <= 0 then offset else offset + 1

advancePos :: SourcePos -> Char -> SourcePos
advancePos (SourcePos file line column offset) c =
  SourcePos file
    (advanceLine line c)
    (advanceColumn column c)
    (advanceOffset offset c)

advancesPos :: SourcePos -> String -> SourcePos
advancesPos (SourcePos file line column offset) s =
  SourcePos file
    (foldl advanceLine line s)
    (foldl advanceColumn column s)
    (foldl advanceOffset offset s)


posProperties :: SourcePos -> [(String, String)]
posProperties (SourcePos file line column offset) =
  (if null file then [] else [("file", file)]) ++
  (if line <= 0 then [] else [("line", show line)]) ++
  (if column <= 0 then [] else [("column", show column)]) ++
  (if offset <= 0 then [] else [("offset", show offset)])

instance Show SourcePos where
  show EOF = "(end of input)"
  show (SourcePos file line column offset) =
    if null showName then showDetails
    else if null showDetails then showName
    else showName ++ " " ++ showDetails
    where
      detail a i = if i <= 0 then "" else a ++ " " ++ show i
      details = [detail "line" line, detail "column" column, detail "offset" offset]
      showDetails =
        case filter (not . null) details of
          [] -> ""
          ds -> "(" ++ intercalate ", " ds ++ ")"
      showName = if null file then "" else "\"" ++ file ++ "\""
