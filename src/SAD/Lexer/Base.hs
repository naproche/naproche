-- |
-- Author: Marcel Schütz (2024)
--
-- The lexer type.


module SAD.Lexer.Base where

import Data.Text.Lazy (Text)
import Data.Void (Void)
import Control.Monad.Trans.State.Strict (evalState, State)
import Text.Megaparsec hiding (State)


type Lexer state result = ParsecT Void Text (State state) result

-- | Run a lexer.
runLexer :: forall state result.
            Lexer state result  -- ^ The lexer to be run
         -> state               -- ^ Initial lexer state
         -> String              -- ^ Label (e.g. file name of input text)
         -> Text                -- ^ Input text to be lexed
         -> Either (ParseErrorBundle Text Void) result
runLexer lexer initState label input = evalState (runParserT lexer label input) initState
