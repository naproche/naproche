-- |
-- Author: Marcel Schütz (2024)
--
-- Tokenizing FTL input.


module SAD.Tokenizer.FTL (tokenize, tokenizePIDE) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.Parser.Token qualified as Token
import SAD.Lexer.FTL
import SAD.Lexer.Error
import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


-- * Tokenizing FTL input

-- | Split an FTL text (together with a starting position) into tokens,
-- discarding all comments.
tokenize :: Position.T -> Text -> String -> [Token.Token]
tokenize pos text label = processLexemes pos text label filterFtl handleError

-- | Essentially the same as "tokenize" to be used inside a PIDE.
tokenizePIDE :: Position.T -> Text -> String -> IO [Token.Token]
tokenizePIDE pos text label = processLexemes pos text label filterFtlPIDE handleErrorPIDE


-- | Remove all comments from a list of tokens.
filterFtl :: [Lexeme] -> [Token.Token]
filterFtl [] = []
filterFtl (lexeme:rest) = case lexemeToToken lexeme of
  Nothing -> filterFtl rest
  Just token -> token : filterFtl rest

-- | Essentially the same as "filterFtl" to be used inside a PIDE.
filterFtlPIDE :: [Lexeme] -> IO [Token.Token]
filterFtlPIDE [] = pure []
filterFtlPIDE (lexeme:rest) = do
  mbToken <- lexemeToTokenPIDE lexeme
  case mbToken of
    Nothing -> filterFtlPIDE rest
    Just token -> fmap (token :) (filterFtlPIDE rest)

-- | Transform a lexeme into a @Maybe@-wrapped token: If the lexeme is a comment,
-- @Nothing@ is returned; otherwise @Just token@ is returned for an appropriate
-- token @token@.
lexemeToToken :: Lexeme -> Maybe Token.Token
lexemeToToken (Comment _ pos) = Nothing
lexemeToToken (EOF pos) = Just $ Token.EOF pos
lexemeToToken (Symbol char pos ws) = Just $ Token.Token {
    Token.tokenText = Text.singleton char,
    Token.tokenPos = pos,
    Token.tokenType = if ws then Token.WhiteSpaceBefore else Token.NoWhiteSpaceBefore
  }
lexemeToToken (Lexeme text pos ws) = Just $ Token.Token {
    Token.tokenText = Text.pack text,
    Token.tokenPos = pos,
    Token.tokenType = if ws then Token.WhiteSpaceBefore else Token.NoWhiteSpaceBefore
  }

-- | Essentially the same as "lexemeToToken" to be used inside a PIDE.
lexemeToTokenPIDE :: Lexeme -> IO (Maybe Token.Token)
lexemeToTokenPIDE (Comment _ pos) = do
  Message.reports [(pos, Markup.comment1)]
  return Nothing
lexemeToTokenPIDE token@(EOF pos) = pure $ lexemeToToken token
lexemeToTokenPIDE token@(Symbol char pos ws) = pure $ lexemeToToken token
lexemeToTokenPIDE token@(Lexeme text pos ws) = pure $ lexemeToToken token
