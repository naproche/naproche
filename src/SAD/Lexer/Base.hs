-- |
-- Author: Marcel Schütz (2024)
--
-- The lexer type.


module SAD.Lexer.Base where

import Data.Text.Lazy (Text)
import Control.Monad.Trans.State.Strict (evalState, State)
import Text.Megaparsec hiding (State)

import Isabelle.Position qualified as Position
import Isabelle.Library (BYTES)


type Lexer error state result = ParsecT error Text (State state) result

-- | Run a lexer.
runLexer :: forall error state result.
            Lexer error state result  -- ^ The lexer to be run
         -> state                     -- ^ Initial lexer state
         -> String                    -- ^ Label (e.g. file name of input text)
         -> Text                      -- ^ Input text to be lexed
         -> Either (ParseErrorBundle Text error) result
runLexer lexer initState label input = evalState (runParserT lexer label input) initState

-- | Take a text together with its starting position and return the position of
-- the whole text
lexemePosition :: BYTES a => a -> Position.T -> Position.T
lexemePosition text pos = let newPos = Position.symbol_explode text pos in
  Position.range_position (pos, newPos)
