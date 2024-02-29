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


tokenizeFtl :: [Lexeme] -> [Token.Token]
tokenizeFtl = concatMap lexemeToToken

-- | Transform a lexeme into a @Maybe@-wrapped token: If the lexeme is a comment,
-- @Nothing@ is returned; otherwise @Just token@ is returned for an appropriate
-- token @token@.
lexemeToToken :: Lexeme -> [Token.Token]
-- Comment:
lexemeToToken (Comment _ pos) = []
-- EOF:
lexemeToToken (EOF pos) =
  let token = Token.EOF pos
  in [token]
-- Symbol:
lexemeToToken (Symbol char pos ws) =
  let token = Token.Token {
        Token.tokenText = Text.singleton char,
        Token.tokenPos = pos,
        Token.tokenType = if ws then Token.WhiteSpaceBefore else Token.NoWhiteSpaceBefore
      }
  in [token]
-- Lexeme:
lexemeToToken (Lexeme text pos ws) =
  let token = Token.Token {
        Token.tokenText = Text.pack text,
        Token.tokenPos = pos,
        Token.tokenType = if ws then Token.WhiteSpaceBefore else Token.NoWhiteSpaceBefore
      }
  in [token]


tokenizeFtlPIDE :: [Lexeme] -> IO [Token.Token]
tokenizeFtlPIDE [] = pure []
tokenizeFtlPIDE (l : ls) = do
  fstTok <- lexemeToTokenPIDE l
  restToks <- tokenizeFtlPIDE ls
  return $ fstTok ++ restToks

-- | Essentially the same as "lexemeToToken" to be used inside a PIDE.
lexemeToTokenPIDE :: Lexeme -> IO [Token.Token]
-- Comment:
lexemeToTokenPIDE (Comment _ pos) = do
  Message.reports [(pos, Markup.comment1)]
  return []
-- EOF:
lexemeToTokenPIDE token@EOF{} = pure $ lexemeToToken token
-- Symbol:
lexemeToTokenPIDE token@Symbol{} = pure $ lexemeToToken token
-- Lexeme:
lexemeToTokenPIDE token@Lexeme{} = pure $ lexemeToToken token
