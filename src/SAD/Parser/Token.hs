-- |
-- Author: Andrei Paskevich (2001 - 2008),
--         Steffen Frerix (2017 - 2018)
--         Marcel Schütz (2024)
--
-- Tokenization of input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token (
  -- * Tokens
  Token (tokenPos, tokenText),

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
import Control.Monad.Extra (concatMapM)
import FTLex.Ftl qualified as Ftl

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
    }
  | EOF { tokenPos :: Position.T }
  deriving (Eq, Ord)

instance Show Token where
  show Token{tokenText = p, tokenPos = s} = show p
  show EOF{} = "EOF"


-- * Converting Lexemes to Tokens

-- | Convert a list of FTL lexemes to tokens and throw PIDE markup reports for
-- all comments.
ftlLexemesToTokens :: [Ftl.Lexeme PIDE_Pos] -> IO [Token]
ftlLexemesToTokens lexemes = do
  tokens <- concatMapM toTokens lexemes
  return $ tokens ++ [EOF Position.none]
  where
    toTokens (Ftl.Symbol char _ pos) =
      pure [Token (Text.singleton char) (fromPIDEPos pos)]
    toTokens (Ftl.Word text _ pos) =
      pure [Token (Text.fromStrict text) (fromPIDEPos pos)]
    toTokens (Ftl.Space _ _) = pure []
    toTokens (Ftl.Comment _ _ pos) = do
      Message.reports [(fromPIDEPos pos, Markup.comment1)]
      return []

-- | Convert a list of TeX lexemes to tokens and throw PIDE markup reports for
-- all comments.
texLexemesToTokens :: [TexLexeme] -> IO [Token]
texLexemesToTokens lexemes = do
  tokens <- concatMapM toTokens lexemes
  return $ tokens ++ [EOF Position.none]
  where
    toTokens (TexWord text pos) =
      pure [Token (Text.fromStrict text) (fromPIDEPos pos)]
    toTokens (TexSpace _) = pure []
    toTokens (TexComment _ pos) = do
      Message.reports [(fromPIDEPos pos, Markup.comment1)]
      return []


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
    dive [t] = [showToken t]
    dive (t : t' : ts) = if noSpaceBetween t t'
      then showToken t : dive (t' : ts)
      else showToken t : " " : dive (t' : ts)
    noSpaceBetween t t' = case Position.offset_of (tokenPos t) of
        Just n -> case Position.offset_of (tokenPos t') of
          Just m -> n == m + 1
          Nothing -> False
        Nothing -> False

-- | A singleton /end of file/ token, i.e. the result of tokenizing an empty
-- document
noTokens :: [Token]
noTokens = [EOF Position.none]

-- | Determines whether a token is an /end of file/ token
isEOF :: Token -> Bool
isEOF EOF{} = True
isEOF _ = False
