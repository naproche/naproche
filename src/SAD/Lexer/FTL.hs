-- |
-- Author: Marcel Schütz (2024)
--
-- Lexing FTL input.


module SAD.Lexer.FTL (Lexeme(..), Error(..), processLexemes) where

import Data.Text.Lazy (Text)
import Control.Monad.State.Class
import Text.Megaparsec hiding (Token, State, token)
import Text.Megaparsec.Char

import SAD.Lexer.Base
import SAD.Lexer.Char
import SAD.Lexer.Error

import Isabelle.Position qualified as Position


-- * FTL-specific Lexer Type

type FtlLexer result = Lexer Error LexerState result

data LexerState = LexerState {
    position :: !Position.T,   -- ^ Current position
    whiteSpaceBefore :: !Bool  -- ^ Whether the current token is prepended by white space
  }

data Lexeme =
    Symbol !Char !Position.T !Bool
  | Lexeme !String !Position.T !Bool
  | Comment !String !Position.T
  | EOF !Position.T

-- | Lex an FTL text and pass the result (either a list of lexemes or an error)
-- to a given function.
processLexemes :: Position.T                          -- ^ starting position of input text
               -> Text                                -- ^ input text
               -> String                              -- ^ label of input text (e.g. its file name)
               -> ([Lexeme] -> a)                     -- ^ function to be applied to resulting lexemes when lexing succeeds
               -> (ParseErrorBundle Text Error -> a)  -- ^ function to be applied to resulting error when lexing fails
               -> a
processLexemes pos text label f e = let initState = LexerState {
    position = pos,
    whiteSpaceBefore = False
  } in
  case runLexer ftlText initState label text of
    Left err -> e err
    Right lexemes -> f lexemes


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
