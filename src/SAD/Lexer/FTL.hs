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

import SAD.Parser.Token qualified as Token
import SAD.Lexer.Base
import SAD.Lexer.Primitives qualified as Primitives
import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


-- * Tokenizing FTL input

-- | Split an FTL text (together with a starting position) into tokens,
-- discarding all comments.
tokenize :: Position.T -> Text -> IO [Token.Token]
tokenize pos text = let initState = LexerState {
    position = pos,
    whiteSpaceBefore = False
  } in
  case runLexer ftlText initState "input" text of
    Left _ -> error "Unknown lexing error."
    Right lexemes -> filterFtl lexemes

-- | Report all comments and remove them from a list of tokens.
filterFtl :: [Lexeme] -> IO [Token.Token]
filterFtl [] = pure []
filterFtl (lexeme:rest) = do
  mbToken <- lexemeToToken lexeme
  case mbToken of
    Nothing -> filterFtl rest
    Just token -> fmap (token :) (filterFtl rest)

lexemeToToken :: Lexeme -> IO (Maybe Token.Token)
lexemeToToken (Comment _ pos) = do
  Message.reports [(pos, Markup.comment1)]
  return Nothing
lexemeToToken (EOF pos) = pure $ Just $ Token.EOF pos
lexemeToToken (Symbol char pos ws) = pure $ Just $ Token.Token {
    Token.tokenText = char,
    Token.tokenPos = pos,
    Token.tokenType = if ws then Token.WhiteSpaceBefore else Token.NoWhiteSpaceBefore
  }
lexemeToToken (Alphanum text pos ws) = pure $ Just $ Token.Token {
    Token.tokenText = text,
    Token.tokenPos = pos,
    Token.tokenType = if ws then Token.WhiteSpaceBefore else Token.NoWhiteSpaceBefore
  }


-- * FTL-specific Lexer Type

type FtlLexer result = Lexer LexerState result

data LexerState = LexerState {
    position :: !Position.T,   -- ^ Current position
    whiteSpaceBefore :: !Bool  -- ^ Whether the current token is prepended by white space
  }

data Lexeme =
    Symbol !Text !Position.T !Bool
  | Alphanum !Text !Position.T !Bool
  | Comment !Text !Position.T
  | EOF !Position.T


-- * FTL Lexers

-- | A ForTheL text in the FTL dialect: Arbitrary many tokens, interspersed with
-- optional white space, until the end of the input text is reached.
ftlText :: FtlLexer [Lexeme]
ftlText = do
  optional whiteSpace
  lexemes <- many $ (comment <|> alphanum <|> symbol) <* optional whiteSpace
  eofLexeme <- endOfInput
  return $ lexemes ++ [eofLexeme]

-- | A lexeme: Longest possible string of alpha-numeric ASCII characters.
alphanum :: FtlLexer Lexeme
alphanum = label "alphanumeric token" $ do
  currentPosition <- gets position
  whiteSpaceBeforeCurrentToken <- gets whiteSpaceBefore
  alphanumText <- Primitives.asciiLexeme
  let newPosition = Position.symbol_explode alphanumText currentPosition
      alphanumPosition = lexemePosition alphanumText currentPosition
      whiteSpaceBeforeNextToken = False
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
  return $ Alphanum alphanumText alphanumPosition whiteSpaceBeforeNextToken

-- | A symbol: Any singleton ASCII symbol character.
symbol :: FtlLexer Lexeme
symbol = label "symbol" $ do
  currentPosition <- gets position
  whiteSpaceBeforeCurrentToken <- gets whiteSpaceBefore
  symbolText <- Primitives.asciiSymbol
  let newPosition = Position.symbol_explode symbolText currentPosition
      symbolPosition = lexemePosition symbolText currentPosition
      whiteSpaceBeforeNextToken = False
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
  return $ Symbol symbolText symbolPosition whiteSpaceBeforeCurrentToken

-- | A line comment: Starts with '#' and ends at the next line break.
comment :: FtlLexer Lexeme
comment = label "comment" $ do
  currentPosition <- gets position
  commentSymbol <- Text.singleton <$> char '#'
  commentText <- Text.concat <$> manyTill Primitives.asciiChar newline
  let lexemeText = commentSymbol <> commentText <> "\n"
      newPosition = Position.symbol_explode lexemeText currentPosition
      commentPosition = lexemePosition lexemeText currentPosition
      whiteSpaceBeforeNextToken = True
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
  return $ Comment commentText commentPosition

-- | The end of the input text.
endOfInput :: FtlLexer Lexeme
endOfInput = label "end of input" $ do
  currentPosition <- gets position
  eof
  return $ EOF currentPosition

-- | White space: Longest possible string of ASCII space characters.
whiteSpace :: FtlLexer ()
whiteSpace = label "white space" $ do
  currentPosition <- gets position
  space <- some spaceChar
  let newPosition = Position.symbol_explode space currentPosition
      whiteSpaceBeforeNextToken = True
  put LexerState{position = newPosition, whiteSpaceBefore = whiteSpaceBeforeNextToken}
