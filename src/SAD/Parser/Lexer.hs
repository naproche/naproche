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

import Flex.Ftl qualified as Ftl
import Flex.Position qualified as Pos
import Flex.Message qualified as Msg
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.Char qualified as Char
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)

import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position


-- * PIDE Setup

newtype PIDE_Pos = PIDE_Pos Position.T deriving (Eq, Ord)

fromPIDEPos :: PIDE_Pos -> Position.T
fromPIDEPos (PIDE_Pos pos) = pos


instance Pos.Pos PIDE_Pos where
  noPos :: PIDE_Pos
  noPos = PIDE_Pos Position.none

  explodeString :: String -> PIDE_Pos -> PIDE_Pos
  explodeString str (PIDE_Pos pos) =
    PIDE_Pos $ Position.symbol_explode_string str pos

  getStringPos :: String -> PIDE_Pos -> PIDE_Pos
  getStringPos str (PIDE_Pos pos) =
    let newPos = Position.symbol_explode str pos
    in PIDE_Pos $ Position.range_position (pos, newPos)


instance Msg.Msg PIDE_Pos IO where
  errorLexer :: PIDE_Pos -> String -> IO a
  errorLexer (PIDE_Pos pos) = Message.errorLexer pos


-- * FTL

-- | @lexFtl pos text label@ lexes an FTL document @text@ with a label @label@
-- (e.g. its file name) starting at position @pos@ in the document.
lexFtl :: PIDE_Pos -> Text -> String -> IO [Ftl.Lexeme PIDE_Pos]
lexFtl pos text label = Ftl.runLexer pos text label Ftl.defaultCatCodes pure


-- * TeX

data TexLexeme =
    TexWord Text PIDE_Pos
  | TexComment Text PIDE_Pos
  | TexSpace PIDE_Pos
  | TexEOF PIDE_Pos

-- Indicates whether the tokenizer is currently inside a forthel environment
data TexState =
    InsideForthelEnv
  | OutsideForthelEnv
  deriving (Eq)

-- | @lexTex pos text label@ lexes a TeX document @text@ with a label @label@
-- (e.g. its file name) starting at position @pos@ in the document.
lexTex :: PIDE_Pos -> Text -> String -> IO [TexLexeme]
lexTex pos text _ = pure $ procToken OutsideForthelEnv pos text
  where
    procToken :: TexState -> PIDE_Pos -> Text -> [TexLexeme]
    procToken OutsideForthelEnv currentPos remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> [TexEOF currentPos]
        Just ('\\', rest)
          | Text.isPrefixOf "begin{forthel}" rest ->
              let newPos = Pos.explodeString "\\begin{forthel}" currentPos
              in procToken InsideForthelEnv newPos $ Text.drop (Text.length "\\begin{forthel}") remainingText
          | Text.isPrefixOf "section{" rest ->
              let (section_name, _) = Text.breakOn "}" $ fromMaybe "" (Text.stripPrefix "section{" rest)
                  token_text = "\\section{" <> section_name <> "}"
                  newPos = Pos.explodeString (Text.unpack token_text) currentPos
                  tokPos = Pos.getStringPos (Text.unpack token_text) currentPos
                  resetpretyping_instruction = [
                      TexWord "[" Pos.noPos,
                      TexWord "resetpretyping" tokPos,
                      TexWord "]" Pos.noPos
                    ]
                  toks = procToken OutsideForthelEnv newPos $ Text.drop (Text.length token_text) remainingText
                in resetpretyping_instruction ++ toks
        Just ('%', rest) -> tok:toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            newPos = Pos.explodeString (Text.unpack comment) currentPos
            tokPos = Pos.getStringPos (Text.unpack comment) currentPos
            tok  = TexComment comment tokPos
            toks = procToken OutsideForthelEnv newPos rest
        Just (c, rest) -> toks
          where
            newPos = Pos.explodeString [c] currentPos
            toks = procToken OutsideForthelEnv newPos rest
    -- When we reach an "\end{forthel}" expression inside a forthen environment,
    -- switch to 'OutsideForthelEnv' mode
    procToken InsideForthelEnv currentPos remainingText
      | start == "\\end{forthel}" = toks
      where
        (start, rest) = Text.splitAt (Text.length "\\end{forthel}") remainingText
        newPos = Pos.explodeString (Text.unpack start) currentPos
        toks = procToken OutsideForthelEnv newPos rest
    -- Process alphanumeric token
    procToken InsideForthelEnv currentPos remainingText
      | not (Text.null lexeme) = tok:toks
      where
        (lexeme, rest) = Text.span Char.isAlphaNum remainingText
        tokPos = Pos.getStringPos (Text.unpack lexeme) currentPos
        newPos = Pos.explodeString (Text.unpack lexeme) currentPos
        tok  = TexWord lexeme tokPos
        toks = procToken InsideForthelEnv newPos rest
    -- Process whitespace
    procToken InsideForthelEnv currentPos remainingText
      | not (Text.null white) = tok : toks
      where
        (white, rest) = Text.span Char.isSpace remainingText
        newPos = Pos.explodeString (Text.unpack white) currentPos
        tokPos = Pos.getStringPos (Text.unpack white) currentPos
        tok = TexSpace tokPos
        toks = procToken InsideForthelEnv newPos rest
    -- Process line break
    procToken InsideForthelEnv currentPos remainingText
      | head == "\\\\" = tok : toks
      where
        (head, rest) = Text.splitAt (Text.length "\\\\") remainingText
        newPos = Pos.explodeString (Text.unpack head) currentPos
        tokPos = Pos.getStringPos (Text.unpack head) currentPos
        tok = TexSpace tokPos
        toks = procToken InsideForthelEnv newPos rest
    -- Display style math mode delimiters
    procToken InsideForthelEnv currentPos remainingText
      | head `elem` ["\\[", "\\]", "\\(", "\\)"] = toks
      where
        (head, rest) = Text.splitAt 2 remainingText
        newPos = Pos.explodeString (Text.unpack head) currentPos
        toks = procToken InsideForthelEnv newPos rest
    -- Process non-alphanumeric symbol or EOF
    procToken InsideForthelEnv currentPos remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> [TexEOF currentPos]
        -- Inline math mode delimiter
        Just ('$', rest) -> procToken InsideForthelEnv (Pos.explodeString "$" currentPos) rest
        -- Comment
        Just ('%', _) -> tok:toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            tokPos = Pos.getStringPos (Text.unpack comment) currentPos
            newPos = Pos.explodeString (Text.unpack comment) currentPos
            tok  = TexComment comment tokPos
            toks = procToken InsideForthelEnv newPos rest
        -- Escaped special character
        Just ('\\', rest)
          | Text.head rest `elem` ['{', '}'] ->
            procToken InsideForthelEnv (Pos.explodeString "\\" currentPos) rest
        -- TeX command
        Just ('\\', rest) -> case name of
          "left" -> toks
          "middle" -> toks
          "right" -> toks
          _ -> tok : toks
          where
            (name, rest') = Text.span Char.isAlpha rest
            command = Text.cons '\\' name
            tokPos = Pos.getStringPos (Text.unpack command) currentPos
            newPos = Pos.explodeString (Text.unpack command) currentPos
            tok = TexWord command tokPos
            toks = procToken InsideForthelEnv newPos rest'
        -- Symbolic token
        Just (c, cs) -> tok:toks
          where
            text = Text.singleton c
            tokPos = Pos.getStringPos (Text.unpack text) currentPos
            newPos = Pos.explodeString (Text.unpack text) currentPos
            tok = TexWord text tokPos
            toks = procToken InsideForthelEnv newPos cs
