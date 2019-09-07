{-
Authors: Steffen Frerix (2017 - 2018)

Parser datatype and monad instance.
-}
{-# LANGUAGE PolymorphicComponents #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}
module SAD.Parser.Base
  ( Parser(..),
    State (..),
    stPosition,
    ParseResult (..),
    Reply (..),
    runP,
    getInput,
    getPos,
    getTokens)
  where

import Control.Monad
#if MIN_VERSION_base(4,9,0)
import qualified Control.Monad.Fail as Fail
#endif
import qualified Control.Applicative as Applicative
import Control.Monad.State.Class


import SAD.Parser.Token
import SAD.Parser.Error
import SAD.Core.SourcePos

import Data.Char
import Data.List

import Debug.Trace

-- Parser state
data State st = State {
  stUser  :: st,
  stInput :: [Token],
  lastPosition :: SourcePos}


stPosition :: State st -> SourcePos
stPosition (State _ (t:ts) _) = tokenPos t
stPosition (State _ _ pos) = pos

-- intermediate parse results
data ParseResult st a = PR { prResult :: a, prState :: State st }

instance Functor (ParseResult st) where
  fmap f pr = pr { prResult = f $ prResult pr }

-- Continutation passing style ambiguity parser
type Continuation st a b =
  ParseError -> [ParseResult st a] -> [ParseResult st a] -> b
type EmptyFail    b = ParseError -> b
type ConsumedFail b = ParseError -> b


newtype Parser st a = Parser {runParser :: forall b .
     State st
  -> Continuation st a b
  -> ConsumedFail b
  -> EmptyFail b
  -> b }


-- instance declarations: functor, applicative, monad, alternative, moandplus

instance Functor (Parser st) where
  fmap f p = Parser $ \ st ok consumedFail err ->
    runParser p st (new ok) consumedFail err
    where
      new ok err emptyOk consumedOk = ok err (map (fmap f) emptyOk) (map (fmap f) consumedOk)

instance Applicative.Applicative (Parser st) where
  pure = return
  (<*>) = ap

instance Monad (Parser st) where
  return x = Parser $ \st ok _ _ ->
      ok (newErrorUnknown (stPosition st)) [PR x st] []

  p >>= f = Parser $ \st ok consumedFail emptyFail ->
    let pok = tryParses f ok consumedFail emptyFail
    in  runParser p st pok consumedFail emptyFail
#if !MIN_VERSION_base(4,9,0)
  fail s = Parser $ \st _ _ emptyFail ->
    emptyFail $ newErrorMessage (newMessage s) (stPosition st)
#else
  fail = Fail.fail

instance Fail.MonadFail (Parser st) where
  fail s = Parser $ \st _ _ emptyFail ->
    emptyFail $ newErrorMessage (newMessage s) (stPosition st)
#endif


-- The reverses are just for debugging to force an intuitive order,
-- but are not necessary at all.
-- This function is simple, but unfriendly to read because of all the
-- accumulators involved. A clearer definition would be welcome.
tryParses :: (a -> Parser st b) -> Continuation st b c -> ConsumedFail c
          -> EmptyFail c -> ParseError -> [ParseResult st a]
          -> [ParseResult st a] ->  c
tryParses f ok consumedFail emptyFail err emptyOk consumedOk = go err [] [] [] [] emptyOk consumedOk
  where
    go accErr accEmptyOk accConsumedOk accConsumedFails accEmptyFails emptyOk consumedOk = case (emptyOk, consumedOk) of

      -- If we have no further input: exit based on the accumulated results
      ([],[]) -> case (accEmptyOk, accConsumedOk) of
        ([], []) -> error "tryParses: parser has empty result"
        ([], _ ) -> consumedFail $ foldl' (<++>) err $ accConsumedFails
        (_ , []) -> emptyFail    $ foldl' (<++>) err $ accEmptyFails ++ accConsumedFails
        (_ , _ ) -> ok accErr (reverse accEmptyOk) (reverse accConsumedOk)

      -- If we have further input first work on the 'emptyOk' results
      ((PR a st'):rs, ys) ->
        let fok ferr feok fcok =
              go (accErr <++> ferr) (reverse feok ++ accEmptyOk) (reverse fcok ++ accConsumedOk) accConsumedFails accEmptyFails rs ys
            fcerr err' = go accErr accEmptyOk accConsumedOk (err':accConsumedFails) accEmptyFails rs ys
            feerr err' = go accErr accEmptyOk accConsumedOk accConsumedFails (err':accEmptyFails) rs ys
        in  runParser (f a) st' fok fcerr feerr

      -- .. and then on the 'consumerOk' ones.
      ([], (PR a st'):rs) ->
        let fok ferr feok fcok =
              go (accErr <+> ferr) accEmptyOk (reverse feok ++ reverse fcok ++ accConsumedOk) accConsumedFails accEmptyFails [] rs
            fcerr err' = go accErr accEmptyOk accConsumedOk (err':accConsumedFails) accEmptyFails [] rs
            feerr err' = go accErr accEmptyOk accConsumedOk (err':accConsumedFails) accEmptyFails [] rs
        in  runParser (f a) st' fok fcerr feerr


instance Applicative.Alternative (Parser st) where
  empty = mzero
  (<|>) = mplus


instance MonadPlus (Parser st) where
  mzero       = Parser $ \st _ _ emptyFail -> emptyFail $ newErrorUnknown (stPosition st)
  mplus m n = Parser $ \st ok consumedFail emptyFail ->
    let meerr err =
          let nok   err' = ok   $ err <+>  err'
              ncerr err' = consumedFail $ err <++> err'
              neerr err' = emptyFail $ err <++> err'
          in  runParser n st nok ncerr neerr
    in  runParser m st ok consumedFail meerr



-- Escaping the parser

---- Reply type
data Reply a = Ok [a] | Error ParseError

---- running the parser
runP :: Parser st a -> State st -> Reply (ParseResult st a)
runP p st = runParser p st ok consumedFail emptyFail
  where
    ok _ emptyOk consumedOk = Ok $ emptyOk ++ consumedOk
    consumedFail err  = Error err
    emptyFail err     = Error err


-- parser state management

instance MonadState st (Parser st) where
  get   = Parser $ \st ok _ _ ->
    ok (newErrorUnknown (stPosition st)) [PR (stUser st) st] []
  put s = Parser $ \st ok consumedFail emptyFail ->
    ok (newErrorUnknown (stPosition st)) [PR () st {stUser = s}] []


getInput :: Parser st [Token]
getInput = Parser $ \st ok _ _ ->
  ok (newErrorUnknown (stPosition st)) [PR (stInput st) st] []

getPos :: Parser st SourcePos
getPos = Parser $ \st ok _ _ ->
  ok (newErrorUnknown (stPosition st)) [PR (stPosition st) st] []

getTokens :: [Token] -> Parser st [Token]
getTokens inp = Parser $ \st ok _ _ ->
  let pos = stPosition st
      toks = takeWhile ( (>) pos . tokenPos ) inp
  in  ok (newErrorUnknown (stPosition st)) [PR toks st] []
