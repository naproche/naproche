-- |
-- Author: Marcel Schütz (2024)
--
-- Abstract lexer type.


module SAD.Lexer.Base where

import Data.Text.Lazy (Text)
import Control.Monad.Trans.State.Strict (evalState, State)
import Text.Megaparsec hiding (State)

import Isabelle.Position qualified as Position


type Lexer errorType stateType resultType = ParsecT errorType Text (State stateType) resultType

-- | Run a lexer and pass the result (either a list of lexemes or an error)
-- to a given function or error handler.
runLexer :: Lexer errorType stateType resultType    -- ^ lexer to run
         -> stateType                               -- ^ initial state
         -> Position.T                              -- ^ starting position of input text
         -> Text                                    -- ^ input text
         -> String                                  -- ^ label of input text (e.g. its file name)
         -> (resultType -> a)                       -- ^ function to be applied to resulting lexemes when lexing succeeds
         -> (ParseErrorBundle Text errorType -> a)  -- ^ function to be applied to resulting error when lexing fails
         -> a
runLexer lexer initState pos text label f e =
  case evalState (runParserT lexer label text) initState of
    Left err -> e err
    Right lexemes -> f lexemes

-- | Take a string together with its starting position and return the position
-- of the whole string
getStringPosition :: String -> Position.T -> Position.T
getStringPosition text pos = let newPos = Position.symbol_explode text pos in
  Position.range_position (pos, newPos)
