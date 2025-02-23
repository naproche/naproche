-- |
-- Module      : SAD.Parser.Token
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Generic tokenization setup


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token (
  Token(..),
  renderTokens,

  Warning(..),
  reportWarnings,
  concatTokWarn,

  handleError,
  unknownError,

  tokensRange,
  tokensPos,
  tokensText,
  showToken,
  mergeTokens,
  composeTokens,
  isEOF,
  noTokens
) where

import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Lazy qualified as Lazy
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set (Set)
import Data.Set qualified as Set
import Data.List
import Data.Bifunctor (bimap)
import Text.Megaparsec hiding (State, Pos, Token)

import SAD.Core.Message qualified as Message
import SAD.Helpers (failureMessage)

import Isabelle.Position qualified as Position


-- * Tokens

-- | A token of a ForTheL text
data Token =
    Token {
      tokenText :: Text
    , tokenPos :: Position.T
    }
  | EOF { tokenPos :: Position.T }
  deriving (Eq, Ord)

-- | Render a list of tokens.
renderTokens :: [Token] -> String
renderTokens tokens = intercalate "\n" $ map renderToken tokens

-- | Render a token.
renderToken :: Token -> String
renderToken (Token text pos) =
  "Token:\n" ++
  "  Text: " ++ show text ++ "\n" ++
  "  Position:\n" ++
  "    Line: " ++ maybe (failureMessage "SAD.Parser.Token.renderToken" "Unknown line") show (Position.line_of pos) ++ "\n" ++
  "    Column: " ++ maybe (failureMessage "SAD.Parser.Token.renderToken" "Unknown column") show (Position.column_of pos) ++ "\n" ++
  "    Offset: " ++ maybe (failureMessage "SAD.Parser.Token.renderToken" "Unknown offset") show (Position.offset_of pos) ++ "\n" ++
  "    End-Offset: " ++ maybe (failureMessage "SAD.Parser.Token.renderToken" "Unknown end-offset") show (Position.end_offset_of pos)
renderToken EOF{} = ""


-- * Warnings

-- | A warning: A message equipped with a position that message refers to.
data Warning = Warning Text Position.T

-- | Report several warnings at once.
reportWarnings :: [Warning] -> IO ()
reportWarnings = foldr ((>>) . reportWarning) (return ())

-- | Report a single warning.
reportWarning :: Warning -> IO ()
reportWarning (Warning text pos) = Message.outputTokenizer Message.WARNING pos text

-- | Concatenate a list of tokens/warnings-pairs.
concatTokWarn :: [([Token], [Warning])] -> ([Token], [Warning])
concatTokWarn [] = ([],[])
concatTokWarn ((xs,ys) : rest) = bimap (xs ++) (ys ++) (concatTokWarn rest)


-- * Error Handling

-- | Report a tokenizing error.
handleError :: (error -> (Text, Position.T)) -> ParseErrorBundle [a] error -> IO b
handleError errorHandler errors = do
  let (errorMsg, errorPos) = showError errors errorHandler
  Message.errorTokenizer errorPos errorMsg

-- | Return an error message and the position of the first error that occured
-- during tokenizing.
showError :: ParseErrorBundle [a] error -> (error -> (Text, Position.T)) -> (Text, Position.T)
showError (ParseErrorBundle parseErrors _) errorHandler = case NonEmpty.head parseErrors of
  TrivialError{} -> unknownError
  FancyError _ errs -> properError errorHandler errs

-- | Located error message for an error that is not handled as a custom error
-- of type "Error" during tokenizing.
unknownError :: (Text, Position.T)
unknownError =
  let msg = Text.pack $ failureMessage "SAD.Parser.Token.unknownError" "Unknown tokenizing error."
      pos = Position.none
  in (msg, pos)

-- | Turn a set of tokenizing errors into an error message.
properError :: (error -> (Text, Position.T)) -> Set (ErrorFancy error) -> (Text, Position.T)
properError errorHandler errs =
  case Set.elems errs of
    [] -> unknownError
    err : _ -> fancyError errorHandler err

-- | Turn a tokenizing error into an error message.
fancyError :: (error -> (Text, Position.T)) -> ErrorFancy error -> (Text, Position.T)
fancyError errorHandler err = case err of
  ErrorFail{} -> unknownError
  ErrorIndentation{} -> unknownError
  ErrorCustom err -> errorHandler err


-- * Legacy Dependencies

-- | Get the end position of a token
tokenEndPos :: Token -> Position.T
tokenEndPos tok@Token{} = Position.symbol_explode (tokenText tok) (tokenPos tok)
tokenEndPos tok@EOF{} = tokenPos tok

-- | The range in which the tokens lie
tokensRange :: [Token] -> Position.Range
tokensRange [] = Position.no_range
tokensRange toks = Position.range (tokenPos $ head toks, tokenEndPos $ last toks)

-- | Get the positon of a token, ranging from the beginnig of the first token to
-- the end of the last one.
tokensPos :: [Token] -> Position.T
tokensPos = Position.range_position . tokensRange

-- | Concatenate the text components of a list of tokens.
tokensText :: [Token] -> Text
tokensText = Text.concat . map tokenText

-- | Merge a list of tokens into a single token.
mergeTokens :: [Token] -> Token
mergeTokens tokens = Token (tokensText tokens) (tokensPos tokens)

-- | Print a token
showToken :: Token -> Lazy.Text
showToken t@Token{} = Lazy.fromStrict $ tokenText t
showToken EOF{} = Lazy.pack "end of input"

-- | Append tokens separated by a single space if they were separated
-- by whitespace before
composeTokens :: [Token] -> Lazy.Text
composeTokens = Lazy.concat . dive
  where
    dive [] = []
    dive [t] = [showToken t]
    dive (t : t' : ts) = if noSpaceBetween t t'
      then showToken t : dive (t' : ts)
      else showToken t : " " : dive (t' : ts)
    noSpaceBetween t t' = case Position.offset_of (tokenPos t) of
        Just n -> case Position.offset_of (tokenPos t') of
          Just m -> n == m + 1
          Nothing -> False
        Nothing -> False

-- | A singleton /end of file/ token, i.e. the result of tokenizing an empty
-- document
noTokens :: [Token]
noTokens = [EOF Position.none]

-- | Determines whether a token is an /end of file/ token
isEOF :: Token -> Bool
isEOF EOF{} = True
isEOF _ = False
