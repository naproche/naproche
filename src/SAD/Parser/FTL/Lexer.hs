-- |
-- Module      : SAD.Parser.FTL.Lexer
-- Copyright   : (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Lexing FTL documents

module SAD.Parser.FTL.Lexer (
  Lexeme,
  lex
) where

import Prelude hiding (lex)
import FTLex.Ftl qualified as FTL

import SAD.Parser.Lexer

import Isabelle.Position qualified as Position
import Isabelle.Bytes qualified as Bytes


type Lexeme = FTL.Lexeme Position.T

-- | @lex pos text@ lexes an FTL document @text@ with initial position @pos@.
lex :: Position.T -> Bytes.Bytes -> IO [Lexeme]
lex pos bytes = do
  text <- pideDecode bytes
  FTL.runLexer pos text (FTL.initState pos codeBlocks)
