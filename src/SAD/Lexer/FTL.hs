-- |
-- Author: Marcel Schütz (2024)
--
-- Lexing FTL input.


module SAD.Lexer.FTL (Lexeme(..), ftlText) where

import Control.Monad.State.Class
import Control.Monad (void)
import Text.Megaparsec
import Text.Megaparsec.Char

import SAD.Lexer.Base
import SAD.Lexer.Char
import SAD.Lexer.Error

import Isabelle.Position qualified as Position


data Lexeme =
    Symbol !Char !Position.T !Bool
  | Lexeme !String !Position.T !Bool
  | Comment !String !Position.T
  | EOF !Position.T

-- | A ForTheL text in the FTL dialect: Arbitrary many tokens, interspersed with
-- optional white space, until the end of the input text is reached.
ftlText :: Lexer [Lexeme]
ftlText = do
  optional whiteSpace
  lexemes <- many $ (comment <|> lexeme <|> symbol <|> catchInvalidChar) <* optional whiteSpace
  eofLexeme <- endOfInput
  return $ lexemes ++ [eofLexeme]

-- | A lexeme: Longest possible string of alpha-numeric ASCII characters.
lexeme :: Lexer Lexeme
lexeme = do
  pos <- gets position
  whiteSpaceBefore <- gets whiteSpaceBefore
  lexeme <- some (satisfy isAlphaNum)
  let newPos = Position.symbol_explode lexeme pos
      lexemePos = getStringPosition lexeme pos
      newWhiteSpaceBefore = False
  put LexerState{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }
  return $ Lexeme lexeme lexemePos whiteSpaceBefore

-- | A symbol: Any singleton ASCII symbol character.
symbol :: Lexer Lexeme
symbol = do
  pos <- gets position
  whiteSpaceBefore <- gets whiteSpaceBefore
  symbol <- satisfy isSymbol
  let newPos = Position.symbol_explode [symbol] pos
      symbolPos = getStringPosition [symbol] pos
      newWhiteSpaceBefore = False
  put LexerState{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }
  return $ Symbol symbol symbolPos whiteSpaceBefore

-- | A line comment: Starts with '#' and ends at the next line break.
comment :: Lexer Lexeme
comment = do
  pos <- gets position
  char '#'
  -- Consume as many characters as possible until either an invalid character,
  -- a vertical space or the end of input is reached:
  commentBody <- many (satisfy isCommentChar)
  -- If an invalid character is reached, chatch it (at the position that has
  -- been reached during the execution of the last line):
  optional $ catchInvalidCharAt (Position.symbol_explode ('#' : commentBody) pos)
  -- If no invalid character is reached, expect a vertical space or the end of
  -- input:
  void (satisfy isVerticalSpace) <|> lookAhead eof
  let comment = "#" ++ commentBody ++ "\n"
      newPos = Position.symbol_explode comment pos
      commentPosition = getStringPosition comment pos
      newWhiteSpaceBefore = True
  put LexerState{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }
  return $ Comment commentBody commentPosition

-- | The end of the input text.
endOfInput :: Lexer Lexeme
endOfInput = do
  currentPosition <- gets position
  eof
  return $ EOF currentPosition

-- | White space: Longest possible string of ASCII space characters.
whiteSpace :: Lexer ()
whiteSpace = do
  pos <- gets position
  space <- some (satisfy isSpace)
  let newPos = Position.symbol_explode space pos
      newWhiteSpaceBefore = True
  put LexerState{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }

-- | Catch an invalid character and report it together with a given position
-- (which is intended to be the position of that character) as a lexing error.
catchInvalidCharAt :: Position.T -> Lexer a
catchInvalidCharAt pos = do
  char <- satisfy isInvalidChar
  let charPos = getStringPosition [char] pos
      err = InvalidChar char charPos
  customFailure err

-- | Catch an invalid character and report it together with the current position
-- (which is intended to be the position of that character) as a lexing error.
catchInvalidChar :: Lexer a
catchInvalidChar = do
  pos <- gets position
  catchInvalidCharAt pos
