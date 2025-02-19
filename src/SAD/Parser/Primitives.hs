-- |
-- Module      : SAD.Parser.Primitives
-- Copyright   : (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Primitive parsers


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Primitives (
  -- * Primitive Token operations
  tokenPrim,
  tokenGuard,
  eof,
  inspectError,
  mapInput,

  -- * Useful macros
  satisfy,
  anyToken,
  word,
  digit,
  symb,
  token,
  token',
  tokenPos',
  tokenOf,
  tokenOf',
  tokenSeq,
  tokenSeq',
  tokenSeqOf,
  tokenSeqOf',
  getToken,
  getToken',
  getTokenOf,
  getTokenOf',
  symbol,
  symbolNotAfterSpace
) where

import Control.Applicative
import Control.Monad (void, guard)
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.Parser.Base
import SAD.Parser.Error
import SAD.Parser.Token
import SAD.Helpers

import Isabelle.Position qualified as Position


-- | Parse the current token or return an @EmptyFail@
-- if the input is empty, eof or the supplied test functions returns @Nothing@.
tokenPrim :: (Token -> Maybe a) -> Parser st a
tokenPrim test = Parser $ \(State st input parserKind _) ok _ eerr ->
  case input of
    []   -> eerr $ unexpectError "" Position.none
    t:ts -> case guard (not $ isEOF t) >> test t of
      Just x  ->
        let newstate = State st ts parserKind (tokenPos t)
            newerr   = newErrorUnknown $ tokenPos t
        in  ok newerr [] [PR x newstate]
      Nothing -> eerr $ unexpectError (showToken t) (tokenPos t)

-- | @tokenGuard test p@ parses the current token using @p@ only if the token
-- passes the predicate @test@. Does not produce particularly useful error
-- messages.
tokenGuard :: (Token -> Bool) -> Parser st a -> Parser st a
tokenGuard test p = Parser $ \st@(State _ input  _ _) ok cerr eerr ->
  case input of
    []   -> eerr $ unexpectError "" Position.none
    t:ts -> if test t
      then runParser p st ok cerr eerr
      else eerr $ unexpectError (showToken t) (tokenPos t)

-- | Parse the end of input
eof :: Parser st ()
eof = Parser $ \(State st input parserKind _) ok _ eerr ->
  case input of
    [] -> eerr $ unexpectError "" Position.none
    (t:ts) ->
      if isEOF t
      then
        let newstate = State st ts parserKind (tokenPos t)
            newerr   = newErrorUnknown $ tokenPos t
        in  ok newerr [] [PR () newstate]
      else eerr $ unexpectError (showToken t) (tokenPos t)

-- Turn @ParseError@s into valid @ParseResult@s.
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


-- | Check if the current token satisfies a predicate; if not fail
satisfy :: (Text -> Bool) -> Parser st Text
satisfy pr = tokenPrim prTest
  where
    prTest :: Token -> Maybe Text
    prTest tk = let s = showToken tk in if pr s then Just s else Nothing

-- | Always succeed and pass on the string of the token
anyToken :: Parser st Text
anyToken = tokenPrim (Just . showToken)

-- | Parses a token that is a word (i.e. consists of only alphabetic characters).
word :: Parser st Text
word = satisfy $ \tk -> Text.all isAsciiLetter tk

-- | Parse a token that is a digit.
digit :: Parser st Text
digit = satisfy (\tk -> Text.length tk == 1 && isAsciiDigit (Text.head tk))

-- | Parse a symbolic token, i.e. a TeX command or a single symbolic character
symb :: Parser st Text
symb = tokenPrim $ \tok ->
  let t = showToken tok
  in case Text.uncons t of
    Just ('\\', rest)
      | Text.all isAsciiLetter rest -> Just t
      | Text.length rest == 1 && Text.all isAsciiSymbol rest -> Just t
    Just (c, "") | isAsciiSymbol c && not (isAsciiPeriod c) -> Just t
    _ -> Nothing


-- | @token tok@ succeeds iff the current token is equal to @tok@. Consumes the
-- token.
{-# INLINE token #-}
token :: Text -> Parser st ()
token tok = void $ satisfy (tok ==)

-- | Case-insensitive version of @token@. The argument is assumed to be in
-- folded case.
{-# INLINE token' #-}
token' :: Text -> Parser st ()
token' tok = void $ satisfy $ (tok ==) . Text.toCaseFold

-- | A version of @token'@ that returns the position of the token instead of
-- @()@.
tokenPos' :: Text -> Parser st Position.T
tokenPos' s = do
  pos <- getPos
  token' s
  return pos

-- | @tokenOf toks@ succeeds iff the current token is an element of @toks@.
-- Consumes the token.
tokenOf :: [Text] -> Parser st ()
tokenOf = void . getTokenOf

-- | A sequence of tokens.
tokenSeq :: [Text] -> Parser st ()
tokenSeq = mapM_ token

-- | @tokenSeqOf tokSeqs@ succeeds iff one of the token sequences in @tokSeq@
-- can be consumed.
tokenSeqOf :: [[Text]] -> Parser st ()
tokenSeqOf = foldr ((<|>) . tokenOf) empty

-- | Case-insensitive version of @tokenOf@. All arguments are assumed to be in
-- folded case.
{-# INLINE tokenOf' #-}
tokenOf' :: [Text] -> Parser st ()
tokenOf' = void . getTokenOf'

-- | Case-insensitive version of @tokenSeq@. All arguments are assumed to be
-- in folded case.
tokenSeq' :: [Text] -> Parser st ()
tokenSeq' = mapM_ token'

-- | Case-insensitive version of @tokenSeqOf@. All arguments are assumed to be
-- in folded case.
tokenSeqOf' :: [[Text]] -> Parser st ()
tokenSeqOf' = foldr ((<|>) . mapM_ token') empty

getToken :: Text -> Parser st Text
getToken = satisfy . (==)

getToken' :: Text -> Parser st Text
getToken' = satisfy . (==) . Text.toCaseFold

-- | @tokenOf toks@ succeeds iff the current token is an element of @toks@.
-- Returns the parsed token.
getTokenOf :: [Text] -> Parser st Text
getTokenOf = satisfy . flip elem

-- | Case-insensitive version of @getTokenOf@. All arguments are assumed to be
-- in folded case.
getTokenOf' :: [Text] -> Parser st Text
getTokenOf' toks = satisfy $ \tok -> Text.toCaseFold tok `elem` toks

-- | Check if the next tokens are the (case-sensitive) characters
-- of the input string. Useful for parsing symbols.
symbol :: Text -> Parser st ()
symbol = mapM_ (token . Text.singleton) . Text.unpack

-- | Same as 'symbol' but the token to be parsed must not be prepended by a
-- white token.
symbolNotAfterSpace :: Text -> Parser st ()
symbolNotAfterSpace s = do
  lastPos <- getLastPos
  let notAfterSpace tok = case Position.offset_of (tokenPos tok) of
        Just n -> case Position.end_offset_of lastPos of
          Just m -> n == m
          Nothing -> False
        Nothing -> False
  tokenGuard notAfterSpace (symbol s)
