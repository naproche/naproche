-- |
-- Authors: Marcel Schütz (2024)
--
-- Lexing

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SAD.Parser.Lexer (
  PIDE_Pos(..),
  fromPIDEPos,
  TexLexeme(..),
  lexFtl,
  lexTex
) where

import FTLex.Ftl qualified as Ftl
import FTLex.Base
import FTLex.Position qualified as Pos
import FTLex.Message qualified as Msg
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Char qualified as Char
import Data.Text.Encoding (encodeUtf8)
import Data.Set (Set)
import Data.Set qualified as Set

import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position


-- * PIDE Setup

newtype PIDE_Pos = PIDE_Pos Position.T deriving (Eq, Ord)

fromPIDEPos :: PIDE_Pos -> Position.T
fromPIDEPos (PIDE_Pos pos) = pos


instance Pos.Pos PIDE_Pos where
  noPos :: PIDE_Pos
  noPos = PIDE_Pos Position.none

  getNextPos :: Text -> PIDE_Pos -> PIDE_Pos
  getNextPos text (PIDE_Pos pos) =
    PIDE_Pos $ Position.symbol_explode text pos

  getPosOf :: Text -> PIDE_Pos -> PIDE_Pos
  getPosOf text (PIDE_Pos pos) =
    let newPos = Position.symbol_explode text pos
    in PIDE_Pos $ Position.range_position (pos, newPos)

  showPos :: PIDE_Pos -> Text
  showPos _ = "position information not provided"


instance Msg.Msg PIDE_Pos IO where
  errorLexer :: PIDE_Pos -> Text -> IO a
  errorLexer (PIDE_Pos pos) = Message.errorLexer pos


-- * FTL

initFtlState :: PIDE_Pos -> Ftl.LexingState PIDE_Pos
initFtlState pos = Ftl.LexingState{
    Ftl.position = pos,
    -- ^ Initial position
    Ftl.catCodes = Ftl.defaultCatCodes ftlUnicodeBlocks,
    -- ^ Initial category codes
    Ftl.unicodeBlocks = ftlUnicodeBlocks
    -- ^ Supported Unicode blocks
  }

-- | Unicode blocks whose characters are recognized by the FTL lexer:
-- * Basic Latin
ftlUnicodeBlocks :: Set UnicodeBlock
ftlUnicodeBlocks = Set.singleton BasicLatin

-- | @lexFtl pos text label@ lexes an FTL document @text@ with a label @label@
-- (e.g. its file name) starting at position @pos@ in the document.
lexFtl :: PIDE_Pos -> Text -> IO [Ftl.Lexeme PIDE_Pos]
lexFtl pos text = Ftl.runLexer pos (encodeUtf8 text) UTF8 (initFtlState pos) LF


-- * TeX

data TexLexeme =
    TexWord Text PIDE_Pos
  | TexComment Text PIDE_Pos
  | TexSpace PIDE_Pos

-- Indicates whether the tokenizer is currently inside a forthel environment
data TexState =
    InsideForthelEnv
  | OutsideForthelEnv
  deriving (Eq)

-- | @lexTex pos text label@ lexes a TeX document @text@ with a label @label@
-- (e.g. its file name) starting at position @pos@ in the document.
lexTex :: PIDE_Pos -> Text -> IO [TexLexeme]
lexTex pos text = pure $ procToken OutsideForthelEnv pos text
  where
    procToken :: TexState -> PIDE_Pos -> Text -> [TexLexeme]
    procToken OutsideForthelEnv currentPos remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> []
        Just ('\\', rest)
          | Text.isPrefixOf "begin{forthel}" rest ->
              let newPos = Pos.getNextPos "\\begin{forthel}" currentPos
              in procToken InsideForthelEnv newPos $ Text.drop (Text.length "\\begin{forthel}") remainingText
          | Text.isPrefixOf "section" rest ->
              let rest' = Text.drop (Text.length "section") rest
              in  if Text.null rest' || not (Char.isAlpha (Text.head rest'))
                  then 
                    let sectionCommand = "\\section"
                        newRest = Text.drop (Text.length sectionCommand) rest
                        newPos = Pos.getNextPos sectionCommand currentPos
                        tokPos = Pos.getPosOf sectionCommand currentPos
                        tok = TexWord sectionCommand tokPos
                        toks = procToken OutsideForthelEnv newPos newRest
                    in tok:toks
                  else 
                    let (commandName, rest'') = Text.span Char.isAlpha rest
                        command = "\\" <> commandName
                        newPos = Pos.getNextPos command currentPos
                    in  procToken OutsideForthelEnv newPos rest''
        Just ('%', rest) -> tok:toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            newPos = Pos.getNextPos comment currentPos
            tokPos = Pos.getPosOf comment currentPos
            tok  = TexComment comment tokPos
            toks = procToken OutsideForthelEnv newPos rest
        Just (c, rest) -> toks
          where
            newPos = Pos.getNextPos (Text.singleton c) currentPos
            toks = procToken OutsideForthelEnv newPos rest
    -- When we reach an "\end{forthel}" expression inside a forthen environment,
    -- switch to 'OutsideForthelEnv' mode
    procToken InsideForthelEnv currentPos remainingText
      | start == "\\end{forthel}" = toks
      where
        (start, rest) = Text.splitAt (Text.length "\\end{forthel}") remainingText
        newPos = Pos.getNextPos start currentPos
        toks = procToken OutsideForthelEnv newPos rest
    -- Process alphanumeric token
    procToken InsideForthelEnv currentPos remainingText
      | not (Text.null lexeme) = tok:toks
      where
        (lexeme, rest) = Text.span Char.isAlphaNum remainingText
        tokPos = Pos.getPosOf lexeme currentPos
        newPos = Pos.getNextPos lexeme currentPos
        tok  = TexWord lexeme tokPos
        toks = procToken InsideForthelEnv newPos rest
    -- Process whitespace
    procToken InsideForthelEnv currentPos remainingText
      | not (Text.null white) = tok : toks
      where
        (white, rest) = Text.span Char.isSpace remainingText
        newPos = Pos.getNextPos white currentPos
        tokPos = Pos.getPosOf white currentPos
        tok = TexSpace tokPos
        toks = procToken InsideForthelEnv newPos rest
    -- Process line break
    procToken InsideForthelEnv currentPos remainingText
      | head == "\\\\" = tok : toks
      where
        (head, rest) = Text.splitAt (Text.length "\\\\") remainingText
        newPos = Pos.getNextPos head currentPos
        tokPos = Pos.getPosOf head currentPos
        tok = TexSpace tokPos
        toks = procToken InsideForthelEnv newPos rest
    -- Display style math mode delimiters
    procToken InsideForthelEnv currentPos remainingText
      | head `elem` ["\\[", "\\]", "\\(", "\\)"] = toks
      where
        (head, rest) = Text.splitAt 2 remainingText
        newPos = Pos.getNextPos head currentPos
        toks = procToken InsideForthelEnv newPos rest
    -- Process non-alphanumeric symbol or EOF
    procToken InsideForthelEnv currentPos remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> []
        -- Inline math mode delimiter
        Just ('$', rest) -> procToken InsideForthelEnv (Pos.getNextPos "$" currentPos) rest
        -- Comment
        Just ('%', _) -> tok:toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            tokPos = Pos.getPosOf comment currentPos
            newPos = Pos.getNextPos comment currentPos
            tok  = TexComment comment tokPos
            toks = procToken InsideForthelEnv newPos rest
        -- Escaped special character
        Just ('\\', rest)
          | Text.head rest `elem` ['{', '}'] ->
            procToken InsideForthelEnv (Pos.getNextPos "\\" currentPos) rest
        -- TeX command
        Just ('\\', rest) -> case name of
          "left" -> toks
          "middle" -> toks
          "right" -> toks
          _ -> tok : toks
          where
            (name, rest') = Text.span Char.isAlpha rest
            command = Text.cons '\\' name
            tokPos = Pos.getPosOf command currentPos
            newPos = Pos.getNextPos command currentPos
            tok = TexWord command tokPos
            toks = procToken InsideForthelEnv newPos rest'
        -- Symbolic token
        Just (c, cs) -> tok:toks
          where
            text = Text.singleton c
            tokPos = Pos.getPosOf text currentPos
            newPos = Pos.getNextPos text currentPos
            tok = TexWord text tokPos
            toks = procToken InsideForthelEnv newPos cs
