{-
Authors: Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Token source positions: counting Unicode codepoints.
-}

module SAD.Core.SourcePos
  ( SourcePos (sourceFile, sourceLine, sourceColumn, sourceOffset, sourceEndOffset),
    SourceRange(SourceRange),
    noPos,
    fileOnlyPos,
    filePos,
    startPos,
    advancePos,
    advanceAlong,
    noRangePos,
    rangePos,
    makeRange,
    noRange)
  where

import qualified Data.List as List

-- | A 'SourcePos' is either a position or a range in the 'sourceFile'.
-- Integer values <= 0 signify 'not given'.
data SourcePos =
  SourcePos {
    sourceFile :: FilePath,
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

advanceLine :: (Ord a, Num a) => a -> Char -> a
advanceLine line c = if line <= 0 || c /= '\n' then line else line + 1
advanceColumn :: (Ord a, Num a) => a -> Char -> a
advanceColumn column c = if column <= 0 then column else if c == '\n' then 1 else column + 1
advanceOffset :: (Ord a, Num a) => a -> p -> a
advanceOffset offset c = if offset <= 0 then offset else offset + 1

advancePos :: SourcePos -> Char -> SourcePos
advancePos (SourcePos file line column offset endOffset) c =
  SourcePos file
    (advanceLine line c)
    (advanceColumn column c)
    (advanceOffset offset c)
    endOffset

advanceAlong :: SourcePos -> String -> SourcePos
advanceAlong = List.foldl' advancePos

data SourceRange = SourceRange SourcePos SourcePos
  deriving (Eq, Show)

noRangePos :: SourcePos -> SourcePos
noRangePos (SourcePos file line column offset _) =
  SourcePos file line column offset 0

rangePos :: SourceRange -> SourcePos
rangePos (SourceRange (SourcePos file line column offset _) ( SourcePos _ _ _ offset' _)) =
  SourcePos file line column offset offset'

makeRange :: (SourcePos, SourcePos) -> SourceRange
makeRange (pos, pos') = SourceRange (rangePos (SourceRange pos pos')) (noRangePos pos')

noRange :: SourceRange
noRange = SourceRange noPos noPos

instance Show SourcePos where
  show (SourcePos file line column _ _) = List.intercalate " " $ filter (not . null) [quotedFilePath, listOfDetails]
    where
      detail a i = if i <= 0 then "" else a ++ " " ++ show i
      details = [detail "line" line, detail "column" column]
      listOfDetails =
        case filter (not . null) details of
          [] -> ""
          ds -> "(" ++ List.intercalate ", " ds ++ ")"
      quotedFilePath = if null file then "" else "\"" ++ file ++ "\""
