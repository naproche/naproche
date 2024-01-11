-- |
-- Author: Andrei Paskevich (2001 - 2008),
--         Steffen Frerix (2017 - 2018)
--         Marcel Schütz (2024)
--
-- Lexing FTL input.


module SAD.Parser.FTL.Lexer (tokenize) where

import Data.Char
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.Parser.Token (Token(..), TokenType(..), isLexeme, makeToken)

import Isabelle.Position qualified as Position


tokenize :: Position.T -> Text -> [Token]
tokenize startPos = processToken startPos NoWhiteSpaceBefore
  where
    processToken :: Position.T -> TokenType -> Text -> [Token]
    -- Process alphanumeric token
    processToken currentPos whitespaceBefore remainingText
      | not (Text.null lexeme) = newTok : toks
      where
        (lexeme, rest) = Text.span isLexeme remainingText
        newPos = Position.symbol_explode lexeme currentPos
        newTok = makeToken lexeme currentPos whitespaceBefore
        toks = processToken newPos NoWhiteSpaceBefore rest
    -- Process whitespace
    processToken currentPos _ remainingText
      | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace remainingText
        newPos = Position.symbol_explode white currentPos
        toks = processToken newPos WhiteSpaceBefore rest
    -- Process EOF, comment or symbolic token
    processToken currentPos whitespaceBefore remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> [EOF currentPos]
        -- Comment
        Just ('#', _) -> newTok : toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            newPos = Position.symbol_explode comment currentPos
            newTok = makeToken comment currentPos Comment
            toks = processToken newPos whitespaceBefore rest
        -- Symbolic token
        Just (c, cs) -> newTok : toks
          where
            symbol = Text.singleton c
            newPos = Position.symbol_explode symbol currentPos
            newTok = makeToken symbol currentPos whitespaceBefore
            toks = processToken newPos NoWhiteSpaceBefore cs
