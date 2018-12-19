{-
Authors: Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Token source positions: counting Unicode codepoints.
-}

module SAD.Core.SourcePos
  ( SourcePos (sourceFile, sourceLine, sourceColumn, sourceOffset, sourceEndOffset),
    SourceRange,
    noPos,
    fileOnlyPos,
    filePos,
    startPos,
    advancePos,
    advancesPos,
    noRangePos,
    rangePos,
    makeRange,
    noRange)
  where

import qualified Data.List as List
import Isabelle.Library


-- positions

data SourcePos =
  SourcePos {
    sourceFile :: String,
    sourceLine :: Int,
    sourceColumn :: Int,
    sourceOffset :: Int,
    sourceEndOffset :: Int }
  deriving (Eq, Ord)

noPos :: SourcePos
noPos = SourcePos "" 0 0 0 0

fileOnlyPos :: String -> SourcePos
fileOnlyPos file = SourcePos file 0 0 0 0

filePos :: String -> SourcePos
filePos file = SourcePos file 1 1 1 0

startPos :: SourcePos
startPos = filePos ""


-- advance position

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


-- ranges: explicit end position

type SourceRange = (SourcePos, SourcePos)

noRangePos :: SourcePos -> SourcePos
noRangePos (SourcePos file line column offset _) =
  SourcePos file line column offset 0

rangePos :: SourceRange -> SourcePos
rangePos (SourcePos file line column offset _, SourcePos _ _ _ offset' _) =
  SourcePos file line column offset offset'

makeRange :: (SourcePos, SourcePos) -> SourceRange
makeRange (pos, pos') = (rangePos (pos, pos'), noRangePos pos')

noRange :: SourceRange
noRange = (noPos, noPos)


-- human-readable output

instance Show SourcePos where
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
          ds -> "(" ++ commas ds ++ ")"
      showName = if null file then "" else "\"" ++ file ++ "\""
