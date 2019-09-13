{-
Authors: Steffen Frerix (2017 - 2018)

Primitive parsers.
-}



module SAD.Parser.Primitives where

import SAD.Parser.Base
import SAD.Parser.Error
import SAD.Parser.Token
import SAD.Core.SourcePos

import Data.Char (isAlpha, toLower)
import Control.Monad (void, guard)


-- primitive Token operations

---- parse the current token
tokenPrim :: (Token -> Maybe a) -> Parser st a
tokenPrim test = Parser $ \(State st input _) ok _ eerr ->
  case input of
    []     -> eerr $ unexpectError "" noSourcePos
    (t:ts) -> case guard (not $ isEOF t) >> test t of
      Just x  ->
        let newstate = State st ts (tokenPos t)
            newerr   = newErrorUnknown $ tokenPos t
        in  ok newerr [] [PR x newstate]
      Nothing -> eerr $ unexpectError (showToken t) (tokenPos t)

---- parse end of input
eof :: Parser st ()
eof = Parser $ \(State st input _) ok _ eerr ->
  case input of
    [] -> eerr $ unexpectError "" noSourcePos
    (t:ts) ->
      if isEOF t
      then
        let newstate = State st ts (tokenPos t)
            newerr   = newErrorUnknown $ tokenPos t
        in  ok newerr [] [PR () newstate]
      else eerr $ unexpectError (showToken t) (tokenPos t)


-- error handling outside of the monad

catchError :: (ParseError -> a) -> Parser st a -> Parser st a
catchError catch p = Parser $ \st ok cerr eerr ->
  let pcerr err = ok (newErrorUnknown $ stPosition st) [] [PR (catch err) st]
      peerr err = ok (newErrorUnknown $ stPosition st) [PR (catch err) st] []
  in  runParser p st ok pcerr peerr

inspectError :: Parser st a -> Parser st (Either ParseError a)
inspectError = catchError Left . fmap Right

jumpWith :: ([Token] -> [Token]) -> Parser st a -> Parser st a
jumpWith jump p = Parser $ \st ok cerr err ->
  let newInput = jump $ stInput st
  in  runParser p st{stInput = newInput} ok cerr err

-- useful macros

---- check if the current token satisfies a predicate; if not fail
satisfy :: (String -> Bool) -> Parser st String
satisfy pr = tokenPrim prTest
  where
    prTest :: Token -> Maybe String
    prTest tk = let s = showToken tk in case (pr s) of
      True  -> Just s
      False -> Nothing

---- check if the current token is a word
word :: Parser st String
word = satisfy $ \tk -> all isAlpha tk

-- | Succeeds iff the current token is equal to @tk@. Consumes the token.
{-# INLINE token #-}
token :: String -> Parser st ()
token tk = void $ satisfy $ \tk' -> tk == tk'

-- | Case-insensitive version of @token@.
{-# INLINE token' #-}
token' :: String -> Parser st ()
token' s = void $ satisfy $ \tk -> s == map toLower tk

-- | @token'@ that return the position of the token instead of @()@.
tokenPos' :: String -> Parser st SourcePos
tokenPos' s = do
  pos <- getPos
  token' s
  return pos

-- | Succeeds iff the current token is an element of @tks@. Consumes the token.
tokenOf :: [String] -> Parser st ()
tokenOf tks = void $ satisfy $ \tk -> tk `elem` tks

-- | Case-insensitive version of @tokenOf@.
{-# INLINE tokenOf' #-}
tokenOf' :: [String] -> Parser st ()
tokenOf' tks = void $ satisfy $ \tk -> map toLower tk `elem` tks

---- check if the next tokens form a given symbol
symbol :: String -> Parser st ()
symbol []     = return ()
symbol (c:cs) = token [c] >> symbol cs

---- always succeed and pass on the string of the token
anyToken :: Parser st String
anyToken = tokenPrim (Just . showToken)
