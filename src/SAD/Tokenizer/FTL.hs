-- |
-- Author: Marcel Schütz (2024)
--
-- Tokenizing FTL input.


module SAD.Tokenizer.FTL (tokenize) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Text.Megaparsec.Error

import SAD.Parser.Token qualified as Token
import SAD.Lexer.FTL
import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


-- * Tokenizing FTL input

-- | Split an FTL text (together with a starting position) into tokens,
-- discarding all comments.
tokenize :: Position.T -> Text -> String -> IO [Token.Token]
tokenize pos text label = processLexemes pos text label filterFtl handleError

handleError :: ParseErrorBundle Text Error -> IO [Token.Token]
handleError err = do
  Message.errorLexer Position.none "Unknown lexing error"

-- | Report all comments and remove them from a list of tokens.
filterFtl :: [Lexeme] -> IO [Token.Token]
filterFtl [] = pure []
filterFtl (lexeme:rest) = do
  mbToken <- lexemeToToken lexeme
  case mbToken of
    Nothing -> filterFtl rest
    Just token -> fmap (token :) (filterFtl rest)

-- | Transform a lexeme into a @Maybe@-wrapped token: If the lexeme is a comment,
-- it is reported and @Nothing@ is returned; otherwise @Just token@ is returned
-- for an appropriate token @token@.
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
