-- |
-- Author: Marcel Schütz (2024)
--
-- Lexing FTL input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Lexer.FTL (tokenize) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Control.Monad.State.Class
import Text.Megaparsec hiding (Token, State, token)
import Text.Megaparsec.Char

import SAD.Parser.Token (Token, TokenType(..), makeToken, makeEOF)
import SAD.Lexer.Base
import SAD.Lexer.Primitives qualified as Primitives

import Isabelle.Position qualified as Position


-- Split an FTL text (together with a starting position) into tokens
tokenize :: Position.T -> Text -> [Token]
tokenize pos text = let initState = LexerState{
    position = pos,
    whiteSpaceBefore = False
  } in
  case runLexer ftlText initState "input" text of
    Left _ -> error "Unknown lexing error."
    Right tokens -> tokens


data LexerState = LexerState {
    position :: Position.T,   -- ^ Current position
    whiteSpaceBefore :: Bool  -- ^ Whether the current token is prepended by white space
  }

type FtlLexer result = Lexer LexerState result

-- | A ForTheL text in the FTL dialect: Arbitrary many tokens, interspersed with
-- optional white space, until the end of the input text is reached.
ftlText :: FtlLexer [Token]
ftlText = do
  optional whiteSpace
  tokens <- many (token <* optional whiteSpace)
  eofToken <- endOfInput
  return $ tokens ++ [eofToken]

-- | A token: A comment, lexeme or symbol.
token :: FtlLexer Token
token = comment <|> lexeme <|> symbol

-- | A lexeme: Longest possible string of alpha-numeric ASCII characters.
lexeme :: FtlLexer Token
lexeme = label "lexeme" $ do
  currentPosition <- gets position
  whiteSpaceBeforeCurrentToken <- gets whiteSpaceBefore
  tokenText <- Primitives.asciiLexeme
  let newPosition = Position.symbol_explode tokenText currentPosition
      whiteSpaceBeforeNextToken = False
      tokenType = if whiteSpaceBeforeCurrentToken then WhiteSpaceBefore else NoWhiteSpaceBefore
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
  return $ makeToken tokenText currentPosition tokenType

-- | A symbol: Any singleton ASCII symbol character.
symbol :: FtlLexer Token
symbol = label "symbol" $ do
  currentPosition <- gets position
  whiteSpaceBeforeCurrentToken <- gets whiteSpaceBefore
  tokenText <- Primitives.asciiSymbol
  let newPosition = Position.symbol_explode tokenText currentPosition
      whiteSpaceBeforeNextToken = False
      tokenType = if whiteSpaceBeforeCurrentToken then WhiteSpaceBefore else NoWhiteSpaceBefore
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
  return $ makeToken tokenText currentPosition tokenType

-- | A line comment: Starts with '#' and ends at the next line break.
comment :: FtlLexer Token
comment = label "comment" $ do
  currentPosition <- gets position
  commentSymbol <- Text.singleton <$> char '#'
  commentText <- Text.concat <$> manyTill Primitives.asciiChar newline
  let tokenText = commentSymbol <> commentText <> "\n"
      newPosition = Position.symbol_explode tokenText currentPosition
      whiteSpaceBeforeNextToken = True
      tokenType = Comment
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
  return $ makeToken tokenText currentPosition tokenType

-- | The end of the input text.
endOfInput :: FtlLexer Token
endOfInput = label "end of input" $ do
  currentPosition <- gets position
  eof
  return $ makeEOF currentPosition

-- | White space: Longest possible string of ASCII space characters.
whiteSpace :: FtlLexer ()
whiteSpace = label "white space" $ do
  currentPosition <- gets position
  space <- some spaceChar
  let newPosition = Position.symbol_explode space currentPosition
      whiteSpaceBeforeNextToken = True
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
