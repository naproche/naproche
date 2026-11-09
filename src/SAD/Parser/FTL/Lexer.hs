{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Parser.FTL.Lexer
-- Description : Lexing FTL documents
-- Copyright   : (c) 2024, Marcel Schütz
-- License     : GPL-3
module SAD.Parser.FTL.Lexer (
  Lexeme,
  lex,
  renderLexemes
) where

import Data.Text (Text)

import FTLex.Ftl qualified as FTL

import Isabelle.Bytes (Bytes)
import Isabelle.Library (cat_lines)
import Isabelle.Position qualified as Position

import Prelude hiding (lex)

import SAD.Export.Pretty
import SAD.Parser.Lexer


type Lexeme = FTL.Lexeme Position.T

-- | @lex pos text@ lexes an FTL document @text@ with initial position @pos@.
lex :: Position.T -> Bytes -> IO [Lexeme]
lex pos bytes = do
  text <- pideDecode bytes
  FTL.runLexer pos text (FTL.initState pos codeBlocks)

-- | Render a list of lexemes.
renderLexemes :: [Lexeme] -> Bytes
renderLexemes tokens = cat_lines $ map renderLexeme tokens

-- | Render a lexeme.
renderLexeme :: Lexeme -> Bytes
renderLexeme (FTL.Symbol content sourceText sourcePos) =
  "Symbol:\n" <>
  renderContent content <> "\n" <>
  renderSourceText sourceText <> "\n" <>
  renderPosition sourcePos
renderLexeme (FTL.Word content sourceText sourcePos) =
  "Word:\n" <>
  renderContent content <> "\n" <>
  renderSourceText sourceText <> "\n" <>
  renderPosition sourcePos
renderLexeme (FTL.Space sourceText sourcePos) =
  "Space:\n" <>
  renderSourceText sourceText <> "\n" <>
  renderPosition sourcePos
renderLexeme (FTL.Comment content sourceText sourcePos) =
  "Comment:\n" <>
  renderContent content <> "\n" <>
  renderSourceText sourceText <> "\n" <>
  renderPosition sourcePos

-- | Render the content of a lexeme.
renderContent :: Pretty a => a -> Bytes
renderContent content = "  Content: " <> pretty_print content

-- | Render the source text of a lexeme.
renderSourceText :: Text -> Bytes
renderSourceText text = "  Source text: " <> pretty_print text

-- | Render the source position of a lexeme.
renderPosition :: Position.T -> Bytes
renderPosition pos =
  "  Source position:\n" <>
  "    Line: " <> maybe "unknown" pretty_print (Position.line_of pos) <> "\n" <>
  "    Column: " <> maybe "unknown" pretty_print (Position.column_of pos) <> "\n" <>
  "    Offset: " <> maybe "unknown" pretty_print (Position.offset_of pos) <> "\n" <>
  "    End-Offset: " <> maybe "unknown" pretty_print (Position.end_offset_of pos)
