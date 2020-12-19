{-
Authors: Steffen Frerix (2017 - 2018)

Primitive parsers.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Primitives
  ( tokenPrim
  , tokenGuard
  , mapInput
  , inspectError
  , satisfy
  , eof
  , word
  , symb
  , anyToken
  , symbol
  , token
  , token'
  , tokenPos'
  , tokenOf
  , tokenOf'
  , getTokenOf
  , getTokenOf'
  ) where

import SAD.Parser.Base
import SAD.Parser.Error
import SAD.Parser.Token
import SAD.Core.SourcePos
import SAD.Data.Formula.Show (symChars)

import Data.Char (isAlpha)
import Control.Monad (void, guard)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text


-- primitive Token operations

-- | Parse the current token or return an @EmptyFail@
-- if the input is empty, eof or the supplied test functions returns @Nothing@.
tokenPrim :: (Token -> Maybe a) -> Parser st a
tokenPrim test = Parser $ \(State st input parserKind _) ok _ eerr ->
  case input of
    []   -> eerr $ unexpectError "" noSourcePos
    t:ts -> case guard (not $ isEOF t) >> test t of
      Just x  ->
        let newstate = State st ts parserKind (tokenPos t)
            newerr   = newErrorUnknown $ tokenPos t
        in  ok newerr [] [PR x newstate]
      Nothing -> eerr $ unexpectError (showToken t) (tokenPos t)


-- | @tokenGuard test p@ parses the current token using @p@ only if the token passes
-- the predicate @test@. Does not produce particularly useful error messages.
tokenGuard :: (Token -> Bool) -> Parser st a -> Parser st a
tokenGuard test p = Parser $ \st@(State _ input  _ _) ok cerr eerr ->
  case input of
    []   -> eerr $ unexpectError "" noSourcePos
    t:ts -> if test t
      then runParser p st ok cerr eerr
      else eerr $ unexpectError (showToken t) (tokenPos t)


-- | Parse the end of input
eof :: Parser st ()
eof = Parser $ \(State st input parserKind _) ok _ eerr ->
  case input of
    [] -> eerr $ unexpectError "" noSourcePos
    (t:ts) ->
      if isEOF t
      then
        let newstate = State st ts parserKind (tokenPos t)
            newerr   = newErrorUnknown $ tokenPos t
        in  ok newerr [] [PR () newstate]
      else eerr $ unexpectError (showToken t) (tokenPos t)


-- | Turn @ParseError@s into valid @ParseResult@s.
catchError :: (ParseError -> a) -> Parser st a -> Parser st a
catchError catch p = Parser $ \st ok _cerr _eerr ->
  let pcerr err = ok (newErrorUnknown $ stPosition st) [] [PR (catch err) st]
      peerr err = ok (newErrorUnknown $ stPosition st) [PR (catch err) st] []
  in  runParser p st ok pcerr peerr

-- | Lift possible parse errors into the @ParseResult@ using @catchError@.
inspectError :: Parser st a -> Parser st (Either ParseError a)
inspectError = catchError Left . fmap Right

-- | Map a function over the input in the Parser @State@.
mapInput :: ([Token] -> [Token]) -> Parser st a -> Parser st a
mapInput jump p = Parser $ \st ok cerr err ->
  let newInput = jump $ stInput st
  in  runParser p st{stInput = newInput} ok cerr err

-- useful macros

-- | Check if the current token satisfies a predicate; if not fail
satisfy :: (Text -> Bool) -> Parser st Text
satisfy pr = tokenPrim prTest
  where
    prTest :: Token -> Maybe Text
    prTest tk = let s = showToken tk in case pr s of
      True  -> Just s
      False -> Nothing

-- | Always succeed and pass on the string of the token
anyToken :: Parser st Text
anyToken = tokenPrim (Just . showToken)

-- | Parses a token that is a word (i.e. consists of only alphabetic characters).
word :: Parser st Text
word = satisfy $ \tk -> Text.all isAlpha tk

symb :: Parser st Text
symb = tokenPrim $ \tok ->
  let t = showToken tok
  in case Text.uncons t of
    Just (c, "") -> guard (c `elem` symChars) >> return t
    _ -> Nothing


-- | @token tok@ succeeds iff the current token is equal to @tok@. Consumes the token.
{-# INLINE token #-}
token :: Text -> Parser st ()
token tok = void $ satisfy (tok ==)

-- | Case-insensitive version of @token@. The argument is assumed to be in folded case.
{-# INLINE token' #-}
token' :: Text -> Parser st ()
token' tok = void $ satisfy $ (tok ==) . Text.toCaseFold

-- | A version of @token'@ that returns the position of the token instead of @()@.
tokenPos' :: Text -> Parser st SourcePos
tokenPos' s = do
  pos <- getPos
  token' s
  return pos

-- | @tokenOf toks@ succeeds iff the current token is an element of @toks@. Consumes the token.
tokenOf :: [Text] -> Parser st ()
tokenOf = void . getTokenOf

-- | Case-insensitive version of @tokenOf@. All arguments are assumed to be in folded case.
{-# INLINE tokenOf' #-}
tokenOf' :: [Text] -> Parser st ()
tokenOf' = void . getTokenOf'

-- | @tokenOf toks@ succeeds iff the current token is an element of @toks@. Returns the parsed token.
getTokenOf :: [Text] -> Parser st Text
getTokenOf = satisfy . flip elem

-- | Case-insensitive version of @getTokenOf@. All arguments are assumed to be in folded case.
getTokenOf' :: [Text] -> Parser st Text
getTokenOf' toks = satisfy $ \tok -> Text.toCaseFold tok `elem` toks

-- | Check if the next tokens are the (case-sensitive) characters
-- of the input string. Useful for parsing symbols.
symbol :: Text -> Parser st ()
symbol = mapM_ (token . Text.singleton) . Text.unpack
