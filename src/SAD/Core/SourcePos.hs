{-
Authors: Steffen Frerix (2017 - 2018), Makarius Wenzel (2018)

Token source positions: counting Unicode codepoints.
-}

module SAD.Core.SourcePos
  ( SourcePos (sourceFile, sourceLine, sourceColumn, sourceOffset, sourceEndOffset),
    SourceRange(SourceRange),
    noSourcePos,
    fileOnlyPos,
    filePos,
    startPos,
    advancePos,
    noRangePos,
    rangePos,
    makeRange,
    noRange)
  where

import SAD.Helpers (notNull)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

import qualified Data.List as List

-- | A 'SourcePos' is either a position or a range in the 'sourceFile'.
-- Integer values <= 0 signify 'not given'.
data SourcePos =
  SourcePos {
    sourceFile :: Text,
    sourceLine :: Int,
    sourceColumn :: Int,
    sourceOffset :: Int,
    sourceEndOffset :: Int }
  deriving (Eq, Ord)

noSourcePos :: SourcePos
noSourcePos = SourcePos Text.empty 0 0 0 0

fileOnlyPos :: Text -> SourcePos
fileOnlyPos file = SourcePos file 0 0 0 0

filePos :: Text -> SourcePos
filePos file = SourcePos file 1 1 1 0

startPos :: SourcePos
startPos = filePos Text.empty


-- advance position

advanceLine :: Int -> Char -> Int
advanceLine line c = if line <= 0 || c /= '\n' then line else line + 1
advanceColumn :: Int -> Char -> Int
advanceColumn column c = if column <= 0 || c == '\r' then column else if c == '\n' then 1 else column + 1
advanceOffset :: Int -> Char -> Int
advanceOffset offset c = if offset <= 0 || c == '\r' then offset else offset + 1

advancePos1 :: SourcePos -> Char -> SourcePos
advancePos1 (SourcePos file line column offset endOffset) c =
  SourcePos file
    (advanceLine line c)
    (advanceColumn column c)
    (advanceOffset offset c)
    endOffset

advancePos :: SourcePos -> Text -> SourcePos
advancePos = Text.foldl' advancePos1

data SourceRange = SourceRange SourcePos SourcePos
  deriving (Eq, Ord, Show)

noRangePos :: SourcePos -> SourcePos
noRangePos (SourcePos file line column offset _) =
  SourcePos file line column offset 0

rangePos :: SourceRange -> SourcePos
rangePos (SourceRange (SourcePos file line column offset _) ( SourcePos _ _ _ offset' _)) =
  SourcePos file line column offset offset'

makeRange :: (SourcePos, SourcePos) -> SourceRange
makeRange (pos, pos') = SourceRange (rangePos (SourceRange pos pos')) (noRangePos pos')

noRange :: SourceRange
noRange = SourceRange noSourcePos noSourcePos

instance Show SourcePos where
  show (SourcePos file line column _ _) = List.intercalate " " $ filter notNull [quotedFilePath, listOfDetails]
    where
      detail a i = if i <= 0 then "" else a ++ " " ++ show i
      details = [detail "line" line, detail "column" column]
      listOfDetails =
        case filter notNull details of
          [] -> ""
          ds -> "(" ++ List.intercalate ", " ds ++ ")"
      quotedFilePath = if Text.null file then "" else "\"" ++ Text.unpack file ++ "\""
