-- |
-- Author: Andrei Paskevich (2001 - 2008),
--         Steffen Frerix (2017 - 2018)
--         Marcel Schütz (2024)
--
-- Tokenization of input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token (
  -- * Tokens
  Token (tokenType, tokenPos, tokenText),
  TokenType (..),

  -- * Converting Lexemes to Tokens
  ftlLexemesToTokens,
  texLexemesToTokens,

  -- * Legacy Dependencies
  tokensRange,
  showToken,
  composeTokens,
  isEOF,
  noTokens
) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Flex.Ftl qualified as Ftl

import SAD.Parser.Lexer
import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


-- * Tokens

-- | A token of a ForTheL text
data Token =
    Token {
      tokenText :: Text
    , tokenPos :: Position.T
    , tokenType :: TokenType
    }
  | EOF { tokenPos :: Position.T }
  deriving (Eq, Ord)

instance Show Token where
  show Token{tokenText = p, tokenPos = s} = show p
  show EOF{} = "EOF"

data TokenType =
    NoWhiteSpaceBefore  -- a regular token without preceding whitespace
  | WhiteSpaceBefore    -- a regular token with preceding whitespace
  | Comment             -- a comment
  deriving (Eq, Ord, Show)


-- * Converting Lexemes to Tokens

-- * FTL

-- | Convert an FTL lexeme together with a flag that indicates whether the
-- lexeme is preceded by whitespace to a token. If the lexeme is a comment,
-- throw an appropriate PIDE markup report.
ftlLexemeToToken :: Ftl.Lexeme PIDE_Pos -> Bool -> IO [Token]
ftlLexemeToToken (Ftl.Symbol char pos) whiteSpaceBefore = pure $
  if whiteSpaceBefore
    then [Token (Text.singleton char) (fromPIDEPos pos) WhiteSpaceBefore]
    else [Token (Text.singleton char) (fromPIDEPos pos) NoWhiteSpaceBefore]
ftlLexemeToToken (Ftl.Word text pos) whiteSpaceBefore = pure $
  if whiteSpaceBefore
    then [Token text (fromPIDEPos pos) WhiteSpaceBefore]
    else [Token text (fromPIDEPos pos) NoWhiteSpaceBefore]
ftlLexemeToToken (Ftl.Space pos) _ = pure []
ftlLexemeToToken (Ftl.Comment _ pos) _ = do
  Message.reports [(fromPIDEPos pos, Markup.comment1)]
  return []
ftlLexemeToToken (Ftl.EOF pos) _ = pure [EOF (fromPIDEPos pos)]

-- | Convert a list of FTL lexemes to tokens and throw PIDE markup reports for
-- all comments.
ftlLexemesToTokens :: [Ftl.Lexeme PIDE_Pos] -> IO [Token]
ftlLexemesToTokens = toTokens False
  where
    toTokens whiteSpaceBefore (lex : lex' : rest) = case lex of
      Ftl.Symbol _ _ -> liftA2 (++)
        (ftlLexemeToToken lex whiteSpaceBefore)
        (toTokens False (lex' : rest))
      Ftl.Word _ _ -> liftA2 (++)
        (ftlLexemeToToken lex whiteSpaceBefore)
        (toTokens False (lex' : rest))
      Ftl.Space _ -> toTokens True (lex' : rest)
      Ftl.Comment _ _ -> liftA2 (++)
        (ftlLexemeToToken lex whiteSpaceBefore)
        (toTokens True (lex' : rest))
      Ftl.EOF _ -> ftlLexemeToToken lex whiteSpaceBefore
    toTokens whiteSpaceBefore [lex] = ftlLexemeToToken lex whiteSpaceBefore
    toTokens _ [] = pure []


-- * TeX

-- | Convert a TeX lexeme together with a flag that indicates whether the
-- lexeme is preceded by whitespace to a token. If the lexeme is a comment,
-- throw an appropriate PIDE markup report.
texLexemeToToken :: TexLexeme -> Bool -> IO [Token]
texLexemeToToken (TexWord text pos) whiteSpaceBefore = pure $
  if whiteSpaceBefore
    then [Token text (fromPIDEPos pos) WhiteSpaceBefore]
    else [Token text (fromPIDEPos pos) NoWhiteSpaceBefore]
texLexemeToToken (TexSpace pos) _ = pure []
texLexemeToToken (TexComment _ pos) _ = do
  Message.reports [(fromPIDEPos pos, Markup.comment1)]
  return []
texLexemeToToken (TexEOF pos) _ = pure [EOF (fromPIDEPos pos)]

-- | Convert a list of TeX lexemes to tokens and throw PIDE markup reports for
-- all comments.
texLexemesToTokens :: [TexLexeme] -> IO [Token]
texLexemesToTokens = toTokens False
  where
    toTokens whiteSpaceBefore (lex : lex' : rest) = case lex of
      TexWord _ _ -> liftA2 (++)
        (texLexemeToToken lex whiteSpaceBefore)
        (toTokens False (lex' : rest))
      TexSpace _ -> toTokens True (lex' : rest)
      TexComment _ _ -> liftA2 (++)
        (texLexemeToToken lex whiteSpaceBefore)
        (toTokens True (lex' : rest))
      TexEOF _ -> texLexemeToToken lex whiteSpaceBefore
    toTokens whiteSpaceBefore [lex] = texLexemeToToken lex whiteSpaceBefore
    toTokens _ [] = pure []


-- * Legacy Dependencies

-- Get the end position of a token
tokenEndPos :: Token -> Position.T
tokenEndPos tok@Token{} = Position.symbol_explode (tokenText tok) (tokenPos tok)
tokenEndPos tok@EOF{} = tokenPos tok

-- | The range in which the tokens lie
tokensRange :: [Token] -> Position.Range
tokensRange [] = Position.no_range
tokensRange toks = Position.range (tokenPos $ head toks, tokenEndPos $ last toks)

-- | Print a token
showToken :: Token -> Text
showToken t@Token{} = tokenText t
showToken EOF{} = Text.pack "end of input"

-- | Append tokens separated by a single space if they were separated
-- by whitespace before
composeTokens :: [Token] -> Text
composeTokens = Text.concat . dive
  where
    dive [] = []
    dive (t:ts) =
      let whitespaceBefore = if tokenType t == WhiteSpaceBefore then Text.singleton ' ' else Text.empty
      in  whitespaceBefore : showToken t : dive ts

-- | A singleton /end of file/ token, i.e. the result of tokenizing an empty
-- document
noTokens :: [Token]
noTokens = [EOF Position.none]

-- | Determines whether a token is an /end of file/ token
isEOF :: Token -> Bool
isEOF EOF{} = True
isEOF _ = False
