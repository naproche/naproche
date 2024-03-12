-- |
-- Author: Marcel Schütz (2024)
--
-- Lexing errors.


module SAD.Lexer.Error (
  handleError,
  handleErrorPIDE
) where

import Text.Megaparsec.Error
import Data.Text.Lazy (Text)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.List.NonEmpty as NonEmpty

import SAD.Core.Message (LocatedMsg, errorLexer)

import Isabelle.Position qualified as Position


-- | Stop execution if an error occured during lexing.
handleError :: (error -> LocatedMsg) -> ParseErrorBundle Text error -> lexingResult
handleError errorHandler errors =
  let (errorMsg, _) = showError errors errorHandler
  in error errorMsg

-- | Report a lexing error.
handleErrorPIDE :: (error -> LocatedMsg) -> ParseErrorBundle Text error -> IO lexingResult
handleErrorPIDE errorHandler errors = do
  let (errorMsg, errorPos) = showError errors errorHandler
  errorLexer errorPos errorMsg

-- | Return an error message and the position of the first error that occured
-- during lexing.
showError :: ParseErrorBundle Text error -> (error -> LocatedMsg) -> LocatedMsg
showError (ParseErrorBundle parseErrors _) errorHandler = case NonEmpty.head parseErrors of
  TrivialError{} -> unknownError
  FancyError _ errs -> properError errorHandler errs

-- | Located error message for an error that is not handled as a custom error
-- of type "Error" during lexing.
unknownError :: LocatedMsg
unknownError =
  let msg =
        "Unknown lexing error. " ++
        "This is likely to be a bug in Naproche. " ++
        "Please file an issue if it has not been reported yet."
      pos = Position.none
  in (msg, pos)

-- | Turn a set of lexing errors into a located error message.
properError :: (error -> LocatedMsg) -> Set (ErrorFancy error) -> LocatedMsg
properError errorHandler errs =
  case Set.elems errs of
    [] -> unknownError
    err : _ -> fancyError errorHandler err

-- | Turn a lexing error into a located error message.
fancyError :: (error -> LocatedMsg) -> ErrorFancy error -> LocatedMsg
fancyError errorHandler err = case err of
  ErrorFail{} -> unknownError
  ErrorIndentation{} -> unknownError
  ErrorCustom err -> errorHandler err
