-- |
-- Author: Andrei Paskevich (2001 - 2008),
--         Steffen Frerix (2017 - 2018)
--
-- Tokenization of input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token (
  -- * Tokens
  Token (..),
  TokenType (..),
  tokensRange,
  showToken,
  isProperToken,
  makeToken,

  -- * Helper functions
  isLexeme,
  reportComments,
  composeTokens,
  isEOF,
  noTokens
) where

import Data.Char
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


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

-- Generate a new token with a given starting position
makeToken :: Text -> Position.T -> TokenType -> Token
makeToken tokenText tokenPos tokenType = let newPos = Position.symbol_explode tokenText tokenPos in
  Token tokenText (Position.range_position (tokenPos, newPos)) tokenType

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

-- | Determine whether a given token is /proper/, i.e. not a comment
isProperToken :: Token -> Bool
isProperToken t@Token{} = case tokenType t of
  NoWhiteSpaceBefore -> True
  WhiteSpaceBefore -> True
  Comment -> False
isProperToken EOF{} = True

isLexeme :: Char -> Bool
isLexeme c = isAscii c && isAlphaNum c

-- | Markup report for comments
reportComments :: Token -> Maybe Position.Report
reportComments t@Token{}
  | isProperToken t = Nothing
  | otherwise = Just (tokenPos t, Markup.comment1)
reportComments EOF{} = Nothing

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
