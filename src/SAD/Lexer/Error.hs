-- |
-- Author: Marcel Schütz (2024)
--
-- Lexing errors.


module SAD.Lexer.Error (
  LocatedErrMsg,
  handleError,
  handleErrorPIDE
) where

import Text.Megaparsec.Error
import Data.Text.Lazy (Text)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.List.NonEmpty as NonEmpty

import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position


-- | A located error message, i.e. an error message together with the position
-- where the respective error occured.
type LocatedErrMsg = (String, Position.T)


-- | Stop execution if an error occured during lexing.
handleError :: (error -> LocatedErrMsg) -> ParseErrorBundle Text error -> lexingResult
handleError errorHandler errors =
  let (errorMsg, _) = showError errors errorHandler
  in error errorMsg

-- | Report a lexing error.
handleErrorPIDE :: (error -> LocatedErrMsg) -> ParseErrorBundle Text error -> IO lexingResult
handleErrorPIDE errorHandler errors = do
  let (errorMsg, errorPos) = showError errors errorHandler
  Message.errorLexer errorPos errorMsg

-- | Return an error message and the position of the first error that occured
-- during lexing.
showError :: ParseErrorBundle Text error -> (error -> LocatedErrMsg) -> LocatedErrMsg
showError (ParseErrorBundle parseErrors _) errorHandler = case NonEmpty.head parseErrors of
  TrivialError{} -> unknownError
  FancyError _ errs -> properError errorHandler errs

-- | Located error message for an error that is not handled as a custom error
-- of type "Error" during lexing.
unknownError :: LocatedErrMsg
unknownError =
  let msg =
        "Unknown lexing error. " ++
        "This is likely to be a bug in Naproche. " ++
        "Please file an issue if it has not been reported yet."
      pos = Position.none
  in (msg, pos)

-- | Turn a set of lexing errors into a located error message.
properError :: (error -> LocatedErrMsg) -> Set (ErrorFancy error) -> LocatedErrMsg
properError errorHandler errs =
  case Set.elems errs of
    [] -> unknownError
    err : _ -> fancyError errorHandler err

-- | Turn a lexing error into a located error message.
fancyError :: (error -> LocatedErrMsg) -> ErrorFancy error -> LocatedErrMsg
fancyError errorHandler err = case err of
  ErrorFail{} -> unknownError
  ErrorIndentation{} -> unknownError
  ErrorCustom err -> errorHandler err
