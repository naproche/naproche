{-
Authors: Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Token source positions.
-}


module Alice.Core.Position
  ( SourcePos (EOF, sourceFile, sourceLine, sourceColumn, sourceOffset, sourceEndOffset),
    SourceRange,
    noPos,
    fileOnlyPos,
    filePos,
    advancePos,
    advancesPos,
    noRangePos,
    rangePos,
    range,
    posProperties)
  where

import Data.List

data SourcePos =
  SourcePos {
    sourceFile :: String,
    sourceLine :: Int,
    sourceColumn :: Int,
    sourceOffset :: Int,
    sourceEndOffset :: Int }
  | EOF
  deriving (Eq, Ord)

type SourceRange = (SourcePos, SourcePos)

noPos :: SourcePos
noPos = SourcePos "" 0 0 0 0

fileOnlyPos :: String -> SourcePos
fileOnlyPos file = SourcePos file 0 0 0 0

filePos :: String -> SourcePos
filePos file = SourcePos file 1 1 1 0

advanceLine line c = if line <= 0 || c /= '\n' then line else line + 1
advanceColumn column c = if column <= 0 then column else if c == '\n' then 1 else column + 1
advanceOffset offset c = if offset <= 0 then offset else offset + 1

advancePos :: SourcePos -> Char -> SourcePos
advancePos (SourcePos file line column offset endOffset) c =
  SourcePos file
    (advanceLine line c)
    (advanceColumn column c)
    (advanceOffset offset c)
    endOffset

advancesPos :: SourcePos -> String -> SourcePos
advancesPos (SourcePos file line column offset endOffset) s =
  SourcePos file
    (foldl advanceLine line s)
    (foldl advanceColumn column s)
    (foldl advanceOffset offset s)
    endOffset

noRangePos :: SourcePos -> SourcePos
noRangePos (SourcePos file line column offset _) =
  SourcePos file line column offset 0

rangePos :: SourceRange -> SourcePos
rangePos (SourcePos file line column offset _, SourcePos _ _ _ offset' _) =
  SourcePos file line column offset offset'

range :: (SourcePos, SourcePos) -> SourceRange
range (pos, pos') = (rangePos (pos, pos'), noRangePos pos')

posProperties :: SourcePos -> [(String, String)]
posProperties (SourcePos file line column offset endOffset) =
  (if null file then [] else [("file", file)]) ++
  (if line <= 0 then [] else [("line", show line)]) ++
  (if column <= 0 then [] else [("column", show column)]) ++
  (if offset <= 0 then [] else [("offset", show offset)]) ++
  (if endOffset <= 0 then [] else [("end_offset", show endOffset)])

instance Show SourcePos where
  show EOF = "(end of input)"
  show (SourcePos file line column _ _) =
    if null showName then showDetails
    else if null showDetails then showName
    else showName ++ " " ++ showDetails
    where
      detail a i = if i <= 0 then "" else a ++ " " ++ show i
      details = [detail "line" line, detail "column" column]
      showDetails =
        case filter (not . null) details of
          [] -> ""
          ds -> "(" ++ intercalate ", " ds ++ ")"
      showName = if null file then "" else "\"" ++ file ++ "\""
