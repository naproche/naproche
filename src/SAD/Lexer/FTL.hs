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
import SAD.Lexer.Char
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
    Token.tokenText = Text.singleton char,
    Token.tokenPos = pos,
    Token.tokenType = if ws then Token.WhiteSpaceBefore else Token.NoWhiteSpaceBefore
  }
lexemeToToken (Lexeme text pos ws) = pure $ Just $ Token.Token {
    Token.tokenText = Text.pack text,
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
    Symbol !Char !Position.T !Bool
  | Lexeme !String !Position.T !Bool
  | Comment !String !Position.T
  | EOF !Position.T


-- * FTL Lexers

-- | A ForTheL text in the FTL dialect: Arbitrary many tokens, interspersed with
-- optional white space, until the end of the input text is reached.
ftlText :: FtlLexer [Lexeme]
ftlText = do
  optional whiteSpace
  lexemes <- many $ (comment <|> lexeme <|> symbol) <* optional whiteSpace
  eofLexeme <- endOfInput
  return $ lexemes ++ [eofLexeme]

-- | A lexeme: Longest possible string of alpha-numeric ASCII characters.
lexeme :: FtlLexer Lexeme
lexeme = do
  pos <- gets position
  whiteSpaceBefore <- gets whiteSpaceBefore
  lexeme <- some (satisfy isAlphaNum)
  let newPos = Position.symbol_explode lexeme pos
      lexemePos = lexemePosition lexeme pos
      newWhiteSpaceBefore = False
  put LexerState{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }
  return $ Lexeme lexeme lexemePos whiteSpaceBefore

-- | A symbol: Any singleton ASCII symbol character.
symbol :: FtlLexer Lexeme
symbol = do
  pos <- gets position
  whiteSpaceBefore <- gets whiteSpaceBefore
  symbol <- satisfy isSymbol
  let newPos = Position.symbol_explode [symbol] pos
      symbolPos = lexemePosition [symbol] pos
      newWhiteSpaceBefore = False
  put LexerState{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }
  return $ Symbol symbol symbolPos whiteSpaceBefore

-- | A line comment: Starts with '#' and ends at the next line break.
comment :: FtlLexer Lexeme
comment = do
  pos <- gets position
  char '#'
  commentBody <- manyTill (satisfy isValidChar) newline
  let comment = "#" ++ commentBody ++ "\n"
      newPos = Position.symbol_explode comment pos
      commentPosition = lexemePosition comment pos
      newWhiteSpaceBefore = True
  put LexerState{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }
  return $ Comment commentBody commentPosition

-- | The end of the input text.
endOfInput :: FtlLexer Lexeme
endOfInput = do
  currentPosition <- gets position
  eof
  return $ EOF currentPosition

-- | White space: Longest possible string of ASCII space characters.
whiteSpace :: FtlLexer ()
whiteSpace = do
  pos <- gets position
  space <- some (satisfy isSpace)
  let newPos = Position.symbol_explode space pos
      newWhiteSpaceBefore = True
  put LexerState{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }
