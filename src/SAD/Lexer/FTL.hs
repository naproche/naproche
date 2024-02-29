-- |
-- Author: Marcel Schütz (2024)
--
-- Lexing FTL input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Lexer.FTL (Lexeme(..), FtlState, lexFtl, lexFtlPIDE) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Control.Monad.State.Class
import Control.Monad (void)
import Text.Megaparsec
import Text.Megaparsec.Char
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map

import SAD.Lexer.Base
import SAD.Lexer.Char
import SAD.Lexer.Error
import SAD.Core.Message (LocatedMsg, warningLexer)

import Isabelle.Position qualified as Position


-- * Lexer type

type FtlLexer resultType = Lexer FtlError FtlState resultType

data Lexeme =
    Symbol !Char !Position.T !Bool
  | Lexeme !String !Position.T !Bool
  | Comment !String !Position.T
  | EOF !Position.T

data FtlState = FtlState{
    position :: !Position.T,                        -- ^ Current position
    whiteSpaceBefore :: !Bool,                      -- ^ Whether the current token is prepended by white space
    commentPrefixes :: ![Text],                     -- ^ Comment prefixes
    delimiters :: !(Map String String),             -- ^ Pairs of opening and closing delimiters
    unclosedDelimiters :: ![(String, Position.T)],  -- ^ All left delimiters that currently lack a corresponding right delimiter
    unopenedDelimiters :: ![(String, Position.T)]   -- ^ All right delimiters that currently lack a corresponding left delimiter
  }

defaultCommentPrefixes :: [Text]
defaultCommentPrefixes = ["#"]

defaultDelimiters :: Map String String
defaultDelimiters = Map.fromList [
    ("(", ")"),
    ("[", "]"),
    ("{", "}")
  ]


-- * Balancing Delimiters

-- | Whether a string is declared as an opening delimiter according to a given
-- state.
isOpeningDelimiter :: FtlState -> String -> Bool
isOpeningDelimiter state string = string `elem` Map.keys (delimiters state)

-- | Whether a string is declared as an opening delimiter according to a given
-- state.
isClosingDelimiter :: FtlState -> String -> Bool
isClosingDelimiter state string = string `elem` Map.elems (delimiters state)

-- | Whether a given string is declared as a delimiter that closes the last
-- opened delimiter.
closesCurrentDelimiter :: FtlState -> String -> Bool
closesCurrentDelimiter state string =
  case unclosedDelimiters state of
    [] -> False
    (delimiter, _) : _ -> case Map.lookup delimiter (delimiters state) of
      Nothing -> False
      Just string' -> string == string'

-- | Add an opening delimiter together with its position to the list of
-- delimiters in a given state that have no corresponding closing delimiter.
addUnclosedDelimiter :: FtlState -> String -> Position.T -> FtlState
addUnclosedDelimiter state delimiter pos =
  state{unclosedDelimiters = (delimiter,pos) : unclosedDelimiters state}

-- | Add a closing delimiter together with its position to the list of
-- delimiters in a given state that have no corresponding opening delimiter.
addUnopenedDelimiter :: FtlState -> String -> Position.T -> FtlState
addUnopenedDelimiter state delimiter pos =
  state{unopenedDelimiters = (delimiter,pos) : unopenedDelimiters state}

-- | Remove the newest delimiter from the list of delimiters in a given state
-- that have no corresponding closing delimiter.
removeUnclosedDelimiter :: FtlState -> FtlState
removeUnclosedDelimiter state = case unclosedDelimiters state of
  [] -> state{unclosedDelimiters = []}
  d : ds -> state{unclosedDelimiters = ds}

-- | Update the list of unopened/unclosed delimiters in a given state:
-- * If a given string closes the latest opened delimiter, then remove this
--   delimiter from the list of unclosed delimiters.
-- * If it is an opening delimiter, add it to the list of unclosed delimiters.
-- * If it is a closing delimiter (that does not close the latest opening
--   delimiter), add it to the list of unopened delimiters.
-- * If it is not any delimiter at all, do nothing.
updateDelimiterState :: FtlState -> String -> Position.T -> FtlState
updateDelimiterState state string pos
  | closesCurrentDelimiter state string = removeUnclosedDelimiter state
  | isOpeningDelimiter state string = addUnclosedDelimiter state string pos
  | isClosingDelimiter state string = addUnopenedDelimiter state string pos
  | otherwise = state


-- * Errors

-- | A lexing error.
data FtlError = InvalidChar !Char !Position.T
  deriving (Eq, Ord)

-- | Turn an error into a located error message.
makeErrMsg :: FtlError -> LocatedMsg
makeErrMsg (InvalidChar char pos) =
  let msg = "Invalid character '" ++ [char] ++ "'."
  in (msg, pos)


-- * Warnings

data FtlWarning =
    UnclosedDelimiter !String !Position.T
  | UnopenedDelimiter !String !Position.T

-- | Turn a warning into a (located) warning message
makeWarnMsg :: FtlWarning -> LocatedMsg
makeWarnMsg (UnclosedDelimiter string pos) =
  let msg = "Missing closing delimiter for '" ++ string ++ "'."
  in (msg, pos)
makeWarnMsg (UnopenedDelimiter string pos) =
  let msg = "Missing opening delimiter for '" ++ string ++ "'."
  in (msg, pos)

-- | Create warnings from a given state
makeWarn :: FtlState -> [FtlWarning]
makeWarn state =
  makeUnclosedDelimiterWarn state ++
  makeUnopenedDelimiterWarn state

-- | Create warnings for all unclosed delimiters stored in a given state
makeUnclosedDelimiterWarn :: FtlState -> [FtlWarning]
makeUnclosedDelimiterWarn state = map (uncurry UnclosedDelimiter) (unclosedDelimiters state)

-- | Create warnings for all unopened delimiters stored in a given state
makeUnopenedDelimiterWarn :: FtlState -> [FtlWarning]
makeUnopenedDelimiterWarn state = map (uncurry UnclosedDelimiter) (unopenedDelimiters state)


-- * Lexer processors

lexFtl :: Position.T -> Text -> String -> [Lexeme]
lexFtl pos text label = runLexer ftlText (initState pos) pos text label fst (handleError makeErrMsg)

lexFtlPIDE :: Position.T -> Text -> String -> IO [Lexeme]
lexFtlPIDE pos text label = runLexer ftlText (initState pos) pos text label (handleWarningsPIDE makeWarnMsg) (handleErrorPIDE makeErrMsg)

-- |
handleWarningsPIDE :: (FtlWarning -> LocatedMsg) -> ([Lexeme], [FtlWarning]) -> IO [Lexeme]
handleWarningsPIDE warningHandler (lexemes, warnings) = do
  let warnMsgs = map warningHandler warnings
  mapM_ (uncurry . flip $ warningLexer) warnMsgs
  return lexemes

initState :: Position.T -> FtlState
initState pos = FtlState{
    position = pos,
    whiteSpaceBefore = False,
    commentPrefixes = defaultCommentPrefixes,
    delimiters = defaultDelimiters,
    unclosedDelimiters = [],
    unopenedDelimiters = []
  }


-- * Lexer combinators

-- | A ForTheL text in the FTL dialect: Arbitrary many tokens, interspersed with
-- optional white space, until the end of the input text is reached.
ftlText :: FtlLexer ([Lexeme], [FtlWarning])
ftlText = do
  optional whiteSpace
  lexemes <- many $ properLexeme <* optional whiteSpace
  eofLexeme <- endOfInput
  state <- get
  let warnings = makeWarn state
  return (lexemes ++ [eofLexeme], warnings)

properLexeme :: FtlLexer Lexeme
properLexeme = choice[
    comment,
    lexeme,
    symbol,
    catchInvalidChar
  ]

-- | A lexeme: Longest possible string of alpha-numeric ASCII characters.
lexeme :: FtlLexer Lexeme
lexeme = do
  state <- get
  pos <- gets position
  delimiters <- gets delimiters
  whiteSpaceBefore <- gets whiteSpaceBefore
  lexeme <- some (satisfy isAlphaNum)
  let newPos = Position.symbol_explode lexeme pos
      lexemePos = getStringPosition lexeme pos
      newWhiteSpaceBefore = False
      newState = updateDelimiterState state lexeme lexemePos
  put newState{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }
  return $ Lexeme lexeme lexemePos whiteSpaceBefore

-- | A symbol: Any singleton ASCII symbol character.
symbol :: FtlLexer Lexeme
symbol = do
  state <- get
  let pos = position state
  whiteSpaceBefore <- gets whiteSpaceBefore
  symbol <- satisfy isSymbol
  let newPos = Position.symbol_explode [symbol] pos
      symbolPos = getStringPosition [symbol] pos
      newWhiteSpaceBefore = False
      newState = updateDelimiterState state [symbol] symbolPos
  put newState{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }
  return $ Symbol symbol symbolPos whiteSpaceBefore

-- | A line comment: Starts with '#' and ends at the next line break.
comment :: FtlLexer Lexeme
comment = do
  state <- get
  let pos = position state
  commentPrefixes <- gets commentPrefixes
  prefix <- Text.unpack <$> choice (map string commentPrefixes)
  -- Consume as many characters as possible until either an invalid character,
  -- a vertical space or the end of input is reached:
  commentBody <- many (satisfy isCommentChar)
  -- If an invalid character is reached, chatch it (at the position that has
  -- been reached during the execution of the last line):
  optional $ catchInvalidCharAt (Position.symbol_explode (prefix <> commentBody) pos)
  -- If no invalid character is reached, expect a vertical space or the end of
  -- input:
  void (satisfy isVerticalSpace) <|> lookAhead eof
  let comment = prefix ++ commentBody ++ "\n"
      newPos = Position.symbol_explode comment pos
      commentPosition = getStringPosition comment pos
      newWhiteSpaceBefore = True
  put state{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }
  return $ Comment commentBody commentPosition

-- | The end of the input text.
endOfInput :: FtlLexer Lexeme
endOfInput = do
  currentPos <- gets position
  eof
  return $ EOF currentPos

-- | White space: Longest possible string of ASCII space characters.
whiteSpace :: FtlLexer ()
whiteSpace = do
  state <- get
  let pos = position state
  space <- some (satisfy isSpace)
  let newPos = Position.symbol_explode space pos
      newWhiteSpaceBefore = True
  put state{
      position = newPos,
      whiteSpaceBefore = newWhiteSpaceBefore
    }

-- | Catch an invalid character and report it together with a given position
-- (which is intended to be the position of that character) as a lexing error.
catchInvalidCharAt :: Position.T -> FtlLexer a
catchInvalidCharAt pos = do
  char <- satisfy isInvalidChar
  let charPos = getStringPosition [char] pos
      err = InvalidChar char charPos
  customFailure err

-- | Catch an invalid character and report it together with the current position
-- (which is intended to be the position of that character) as a lexing error.
catchInvalidChar :: FtlLexer a
catchInvalidChar = do
  pos <- gets position
  catchInvalidCharAt pos
