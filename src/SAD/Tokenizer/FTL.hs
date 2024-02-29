-- |
-- Author: Marcel Schütz (2024)
--
-- Tokenizing FTL input.


module SAD.Tokenizer.FTL (tokenizeFtl, tokenizeFtlPIDE) where

import Data.Text.Lazy qualified as Text

import SAD.Parser.Token qualified as Token
import SAD.Lexer.FTL
import SAD.Core.Message qualified as Message

import Isabelle.Markup qualified as Markup


-- * Tokenizing FTL input

-- | Remove all comments from a list of tokens.
tokenizeFtl :: [Lexeme] -> [Token.Token]
tokenizeFtl [] = []
tokenizeFtl (lexeme:rest) = case lexemeToToken lexeme of
  Nothing -> tokenizeFtl rest
  Just token -> token : tokenizeFtl rest

-- | Essentially the same as "filterFtl" to be used inside a PIDE.
tokenizeFtlPIDE :: [Lexeme] -> IO [Token.Token]
tokenizeFtlPIDE [] = pure []
tokenizeFtlPIDE (lexeme:rest) = do
  mbToken <- lexemeToTokenPIDE lexeme
  case mbToken of
    Nothing -> tokenizeFtlPIDE rest
    Just token -> fmap (token :) (tokenizeFtlPIDE rest)

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
