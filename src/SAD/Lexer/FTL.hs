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
tokenize pos text = let initState = LexerState{position = pos, whiteSpaceBefore = False} in
  case runLexer ftlText initState "input" text of
    Left _ -> error "Unknown lexing error."
    Right tokens -> tokens


data LexerState = LexerState {
    position :: Position.T,
    whiteSpaceBefore :: Bool
  }

type FtlLexer result = Lexer LexerState result

ftlText :: FtlLexer [Token]
ftlText = do
  optional whiteSpace
  tokens <- many (token <* optional whiteSpace)
  eofToken <- endOfInput
  return $ tokens ++ [eofToken]

token :: FtlLexer Token
token = comment <|> lexeme <|> symbol

lexeme :: FtlLexer Token
lexeme = label "lexeme" $ do
  currentPosition <- gets position
  whiteSpaceBeforeCurrentToken <- gets whiteSpaceBefore
  tokenText <- Primitives.asciiAlphaNum
  let newPosition = Position.symbol_explode tokenText currentPosition
      whiteSpaceBeforeNextToken = False
      tokenType = if whiteSpaceBeforeCurrentToken then WhiteSpaceBefore else NoWhiteSpaceBefore
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
  return $ makeToken tokenText currentPosition tokenType

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

comment :: FtlLexer Token
comment = label "comment" $ do
  currentPosition <- gets position
  char '#'
  comment <- Text.concat <$> manyTill Primitives.asciiChar newline
  let tokenText = "#" <> comment <> "\n"
      newPosition = Position.symbol_explode tokenText currentPosition
      whiteSpaceBeforeNextToken = True
      tokenType = Comment
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
  return $ makeToken tokenText currentPosition tokenType

endOfInput :: FtlLexer Token
endOfInput = label "end of input" $ do
  currentPosition <- gets position
  eof
  return $ makeEOF currentPosition

whiteSpace :: FtlLexer ()
whiteSpace = label "white space" $ do
  currentPosition <- gets position
  whiteSpaceBeforeCurrentToken <- gets whiteSpaceBefore
  space <- some spaceChar
  let newPosition = Position.symbol_explode space currentPosition
      whiteSpaceBeforeNextToken = True
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
