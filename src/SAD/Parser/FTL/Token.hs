-- |
-- Module      : SAD.Parser.FTL.Token
-- Copyright   : (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Tokenization of input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.FTL.Token (
  tokenize
) where

import Data.Text qualified as Text
import Data.Text (Text)
import FTLex.Ftl
import Control.Monad.Trans.State.Strict (evalState, State)
import Text.Megaparsec hiding (State, Token, token)
import Control.Monad (unless)

import SAD.Parser.Token
import SAD.Parser.FTL.Lexer qualified as FTL
import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


-- * Tokenizing an FTL document

-- | Convert a list of lexemes to tokens.
tokenize :: [FTL.Lexeme] -> IO [Token]
tokenize lexemes = do
  filteredLexems <- filterLexemes lexemes
  case evalState (runParserT document "" filteredLexems) () of
    Left err -> handleError makeErrMsg err
    Right tokens -> return tokens

-- | Take a list of lexemes, report all comments and remove all comments and
-- spaces from the list.
filterLexemes :: [FTL.Lexeme] -> IO [FTL.Lexeme]
filterLexemes [] = return []
filterLexemes (l : ls) = case l of
  Comment{sourcePos = pos} -> do
    Message.reports [(pos, Markup.comment1)]
    filterLexemes ls
  Space{} -> filterLexemes ls
  _ -> fmap (l :) (filterLexemes ls)


-- * Tokenizing Errors and Warnings

data Error = InvalidIsabelleSymbol Position.T Text
  deriving (Eq, Ord)

-- | Turn an error into a located error 
makeErrMsg :: Error -> (Text, Position.T)
makeErrMsg (InvalidIsabelleSymbol pos text) =
  let msg = "Invalid Isabelle symbol " <> text <> "."
  in (msg, pos)


-- * Tokenizers

type Tokenizer a = ParsecT Error [FTL.Lexeme] (State ()) a

-- | Parse a whole FTL document.
document :: Tokenizer [Token]
document = do
  tokens <- concat <$> many token
  eof
  return $ tokens ++ [EOF Position.none]

-- | Parse a single token.
token :: Tokenizer [Token]
token = choice [
    symbol,
    isabelleSymbol,
    word
  ]

-- | Parse a single symbol.
symbol :: Tokenizer [Token]
symbol = do
  symbol <- satisfy isSymbolLexeme
  let text = Text.singleton $ symbolContent symbol
      pos = sourcePos symbol
  return [Token text pos]

-- | Parse a single symbol.
isabelleSymbol :: Tokenizer [Token]
isabelleSymbol = do
  isabelleSymbol <- satisfy isIsabelleSymbolLexeme
  let identifier = isabelleSymbolContent isabelleSymbol
      text = "\\<" <> identifier <> ">"
      pos = sourcePos isabelleSymbol
  unless (identifier `elem` isabelleSymbols) $
    customFailure (InvalidIsabelleSymbol pos text)
  return [Token text pos]

-- | Parse a single word.
word :: Tokenizer [Token]
word = do
  word <- satisfy isWordLexeme
  let text = wordContent word
      pos = sourcePos word
  return [Token text pos]
