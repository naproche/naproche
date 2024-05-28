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

import Flex.Lexer qualified as Flex
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


instance Flex.Pos PIDE_Pos where
  noPos :: PIDE_Pos
  noPos = PIDE_Pos Position.none

  explodeString :: String -> PIDE_Pos -> PIDE_Pos
  explodeString str (PIDE_Pos pos) =
    PIDE_Pos $ Position.symbol_explode_string str pos

  getStringPos :: String -> PIDE_Pos -> PIDE_Pos
  getStringPos str (PIDE_Pos pos) =
    let newPos = Position.symbol_explode str pos
    in PIDE_Pos $ Position.range_position (pos, newPos)


instance Flex.Msg PIDE_Pos IO where
  errorLexer :: PIDE_Pos -> String -> IO a
  errorLexer (PIDE_Pos pos) = Message.errorLexer pos


-- * FTL

-- | @lexFtl pos text label@ lexes an FTL document @text@ with a label @label@
-- (e.g. its file name) starting at position @pos@ in the document.
lexFtl :: PIDE_Pos -> Text -> String -> IO [Flex.Lexeme PIDE_Pos]
lexFtl pos text label = Flex.runFtlLexer pos text label ftlCatCodes pure

-- | Default category code mapping for FTL documents:
--
-- * The ASCII space character has category @SpaceCat@.
-- * The carriage return has category @LineBreakCat@.
-- * Alphanumeric ASCII characters have category @AlphaNumCat@.
-- * ASCII symbols except @#@ have category @SymbolCat@.
-- * @#@ has category @CommentPrefixCat@.
-- * Any other ASCII characters has category @InvalidCat@.
-- * Any other characters are not in that mapping.
ftlCatCodes :: Flex.CatCodeMap
ftlCatCodes = Map.fromAscList
  [(c, initCatCode c) | c <- ['\NUL' .. '\DEL']]
  where
    initCatCode :: Char -> Flex.CatCode
    initCatCode ' ' = Flex.SpaceCat
    initCatCode '\n' = Flex.LineBreakCat
    initCatCode c
      | Char.isAsciiUpper c = Flex.AlphaNumCat
      | Char.isAsciiLower c = Flex.AlphaNumCat
      | Char.isDigit c = Flex.AlphaNumCat
    initCatCode c
      | '\x21' <= c && c <= '\x22' = Flex.SymbolCat -- ! "
      | '\x24' <= c && c <= '\x2f' = Flex.SymbolCat -- $ % & ' ( ) * + , - . /
      | '\x3a' <= c && c <= '\x40' = Flex.SymbolCat -- : ; < = > ? @
      | '\x5b' <= c && c <= '\x60' = Flex.SymbolCat -- [ \ ] ^ _ `
      | '\x7b' <= c && c <= '\x7e' = Flex.SymbolCat -- { | } ~
    initCatCode '#' = Flex.CommentPrefixCat
    initCatCode _ = Flex.InvalidCat


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
              let newPos = Flex.explodeString "\\begin{forthel}" currentPos
              in procToken InsideForthelEnv newPos $ Text.drop (Text.length "\\begin{forthel}") remainingText
          | Text.isPrefixOf "section{" rest ->
              let (section_name, _) = Text.breakOn "}" $ fromMaybe "" (Text.stripPrefix "section{" rest)
                  token_text = "\\section{" <> section_name <> "}"
                  newPos = Flex.explodeString (Text.unpack token_text) currentPos
                  tokPos = Flex.getStringPos (Text.unpack token_text) currentPos
                  resetpretyping_instruction = [
                      TexWord "[" Flex.noPos,
                      TexWord "resetpretyping" tokPos,
                      TexWord "]" Flex.noPos
                    ]
                  toks = procToken OutsideForthelEnv newPos $ Text.drop (Text.length token_text) remainingText
                in resetpretyping_instruction ++ toks
        Just ('%', rest) -> tok:toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            newPos = Flex.explodeString (Text.unpack comment) currentPos
            tokPos = Flex.getStringPos (Text.unpack comment) currentPos
            tok  = TexComment comment tokPos
            toks = procToken OutsideForthelEnv newPos rest
        Just (c, rest) -> toks
          where
            newPos = Flex.explodeString [c] currentPos
            toks = procToken OutsideForthelEnv newPos rest
    -- When we reach an "\end{forthel}" expression inside a forthen environment,
    -- switch to 'OutsideForthelEnv' mode
    procToken InsideForthelEnv currentPos remainingText
      | start == "\\end{forthel}" = toks
      where
        (start, rest) = Text.splitAt (Text.length "\\end{forthel}") remainingText
        newPos = Flex.explodeString (Text.unpack start) currentPos
        toks = procToken OutsideForthelEnv newPos rest
    -- Process alphanumeric token
    procToken InsideForthelEnv currentPos remainingText
      | not (Text.null lexeme) = tok:toks
      where
        (lexeme, rest) = Text.span Char.isAlphaNum remainingText
        tokPos = Flex.getStringPos (Text.unpack lexeme) currentPos
        newPos = Flex.explodeString (Text.unpack lexeme) currentPos
        tok  = TexWord lexeme tokPos
        toks = procToken InsideForthelEnv newPos rest
    -- Process whitespace
    procToken InsideForthelEnv currentPos remainingText
      | not (Text.null white) = tok : toks
      where
        (white, rest) = Text.span Char.isSpace remainingText
        newPos = Flex.explodeString (Text.unpack white) currentPos
        tokPos = Flex.getStringPos (Text.unpack white) currentPos
        tok = TexSpace tokPos
        toks = procToken InsideForthelEnv newPos rest
    -- Process line break
    procToken InsideForthelEnv currentPos remainingText
      | head == "\\\\" = tok : toks
      where
        (head, rest) = Text.splitAt (Text.length "\\\\") remainingText
        newPos = Flex.explodeString (Text.unpack head) currentPos
        tokPos = Flex.getStringPos (Text.unpack head) currentPos
        tok = TexSpace tokPos
        toks = procToken InsideForthelEnv newPos rest
    -- Display style math mode delimiters
    procToken InsideForthelEnv currentPos remainingText
      | head `elem` ["\\[", "\\]", "\\(", "\\)"] = toks
      where
        (head, rest) = Text.splitAt 2 remainingText
        newPos = Flex.explodeString (Text.unpack head) currentPos
        toks = procToken InsideForthelEnv newPos rest
    -- Process non-alphanumeric symbol or EOF
    procToken InsideForthelEnv currentPos remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> [TexEOF currentPos]
        -- Inline math mode delimiter
        Just ('$', rest) -> procToken InsideForthelEnv (Flex.explodeString "$" currentPos) rest
        -- Comment
        Just ('%', _) -> tok:toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            tokPos = Flex.getStringPos (Text.unpack comment) currentPos
            newPos = Flex.explodeString (Text.unpack comment) currentPos
            tok  = TexComment comment tokPos
            toks = procToken InsideForthelEnv newPos rest
        -- Escaped special character
        Just ('\\', rest)
          | Text.head rest `elem` ['{', '}'] ->
            procToken InsideForthelEnv (Flex.explodeString "\\" currentPos) rest
        -- TeX command
        Just ('\\', rest) -> case name of
          "left" -> toks
          "middle" -> toks
          "right" -> toks
          _ -> tok : toks
          where
            (name, rest') = Text.span Char.isAlpha rest
            command = Text.cons '\\' name
            tokPos = Flex.getStringPos (Text.unpack command) currentPos
            newPos = Flex.explodeString (Text.unpack command) currentPos
            tok = TexWord command tokPos
            toks = procToken InsideForthelEnv newPos rest'
        -- Symbolic token
        Just (c, cs) -> tok:toks
          where
            text = Text.singleton c
            tokPos = Flex.getStringPos (Text.unpack text) currentPos
            newPos = Flex.explodeString (Text.unpack text) currentPos
            tok = TexWord text tokPos
            toks = procToken InsideForthelEnv newPos cs
