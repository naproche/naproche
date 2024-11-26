-- |
-- Module      : SAD.Parser.TEX.Lexer
-- Copyright   : (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Lexing FTL-TeX documents

module SAD.Parser.TEX.Lexer (
  Lexeme,
  lex
) where

import Prelude hiding (lex)
import FTLex.Tex qualified as TEX

import SAD.Parser.Lexer

import Isabelle.Position qualified as Position
import Isabelle.Bytes qualified as Bytes


type Lexeme = TEX.Lexeme Position.T

-- | @lexTex pos text@ lexes a TEX document @text@ with initial position @pos@.
lex :: Position.T -> Bytes.Bytes -> IO [Lexeme]
lex pos bytes = do
  text <- pideDecode bytes
  TEX.runLexer pos text (TEX.initState pos codeBlocks)
