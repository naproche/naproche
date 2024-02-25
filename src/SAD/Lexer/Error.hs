-- |
-- Author: Marcel Schütz (2024)
--
-- Lexing errors.


module SAD.Lexer.Error (
  Error(..),
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

-- | A lexing error.
data Error = InvalidChar !Char !Position.T
  deriving (Eq, Ord)

-- | Stop execution if an error occured during lexing.
handleError :: ParseErrorBundle Text Error -> a
handleError errors = let (errorMsg, _) = showError errors in error errorMsg

-- | Report a lexing error.
handleErrorPIDE :: ParseErrorBundle Text Error -> IO a
handleErrorPIDE errors = do
  let (errorMsg, errorPos) = showError errors
  Message.errorLexer errorPos errorMsg

-- | Return an error message and the position of the first error that occured
-- during lexing.
showError :: ParseErrorBundle Text Error -> LocatedErrMsg
showError (ParseErrorBundle parseErrors _) = case NonEmpty.head parseErrors of
  TrivialError{} -> unknownError
  FancyError _ errs -> properError errs

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
properError :: Set (ErrorFancy Error) -> LocatedErrMsg
properError errs =
  case Set.elems errs of
    [] -> unknownError
    err : _ -> fancyError err

-- | Turn a lexing error into a located error message.
fancyError :: ErrorFancy Error -> LocatedErrMsg
fancyError err = case err of
  ErrorFail{} -> unknownError
  ErrorIndentation{} -> unknownError
  ErrorCustom err -> customError err

-- | Turn a custom error into a located error message.
customError :: Error -> LocatedErrMsg
customError (InvalidChar char pos) =
  let errMsg = "Invalid character '" ++ [char] ++ "'."
      errPos = pos
  in (errMsg, errPos)
