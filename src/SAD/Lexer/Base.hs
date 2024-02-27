-- |
-- Author: Marcel Schütz (2024)
--
-- Abstract lexer type.


module SAD.Lexer.Base where

import Data.Text.Lazy (Text)
import Control.Monad.Trans.State.Strict (evalState, State)
import Text.Megaparsec hiding (State)

import SAD.Lexer.Error

import Isabelle.Position qualified as Position


type Lexer result = ParsecT Error Text (State LexerState) result

data LexerState = LexerState {
    position :: !Position.T,   -- ^ Current position
    whiteSpaceBefore :: !Bool  -- ^ Whether the current token is prepended by white space
  }

initState :: Position.T -> LexerState
initState pos = LexerState {
    position = pos,
    whiteSpaceBefore = False
  }

-- | Run a lexer and pass the result (either a list of lexemes or an error)
-- to a given function or error handler.
runLexer :: Lexer [result]                      -- ^ lexer to run
         -> Position.T                          -- ^ starting position of input text
         -> Text                                -- ^ input text
         -> String                              -- ^ label of input text (e.g. its file name)
         -> ([result] -> a)                     -- ^ function to be applied to resulting lexemes when lexing succeeds
         -> (ParseErrorBundle Text Error -> a)  -- ^ function to be applied to resulting error when lexing fails
         -> a
runLexer lexer pos text label f e =
  case evalState (runParserT lexer label text) (initState pos) of
    Left err -> e err
    Right lexemes -> f lexemes

-- | Take a string together with its starting position and return the position
-- of the whole string
getStringPosition :: String -> Position.T -> Position.T
getStringPosition text pos = let newPos = Position.symbol_explode text pos in
  Position.range_position (pos, newPos)
