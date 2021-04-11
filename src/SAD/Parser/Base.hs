{-
Authors: Steffen Frerix (2017 - 2018)

Parser datatype and monad instance.
-}

{-# LANGUAGE PolymorphicComponents #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}

module SAD.Parser.Base
  ( Parser(..),
    ParseOut(..),
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
import qualified Control.Monad.Fail as Fail
import Control.Applicative
import Control.Monad.State.Class (MonadState(put, get))

import SAD.Parser.Token
import SAD.Parser.Error
import SAD.Core.SourcePos
import SAD.Data.Instr (ParserKind)

import Data.List
import qualified Data.Text as Text


-- | Parser state
data State st = State
  { stUser  :: st
  , stInput :: [Token]
  , parserKind :: ParserKind
  , lastPosition :: SourcePos
  } deriving (Eq, Ord, Show)

-- | Get the current position of the parser.
stPosition :: State st -> SourcePos
stPosition State{ stInput = t:_ } = tokenPos t
stPosition State{ lastPosition = pos } = pos

-- | Intermediate parse results
data ParseResult st a = PR { prResult :: a, prState :: State st }
  deriving (Eq, Ord, Show, Functor)

-- | Ambiguity parser
-- In practice: @st@ = @FState@, @r@ = @ParseResult FState a@
data ParseOut st a 
  = Continuation ParseError [ParseResult st a] [ParseResult st a]
  | ConsumedFail ParseError
  | EmptyFail ParseError
  deriving (Eq, Ord, Show)

newtype Parser st a = Parser {runParser :: State st -> ParseOut st a }

instance Functor (Parser st) where
  fmap f (Parser p) = Parser $ \st -> case p st of
    Continuation err emptyOk consumedOk -> 
      Continuation err (map (fmap f) emptyOk) (map (fmap f) consumedOk)
    ConsumedFail err -> ConsumedFail err
    EmptyFail err -> EmptyFail err

instance Applicative (Parser st) where
  pure = return
  (<*>) = ap

instance Monad (Parser st) where
  return x = Parser $ \st -> Continuation (newErrorUnknown (stPosition st)) [PR x st] []

  (Parser p) >>= f = Parser $ \st -> case p st of
    Continuation err eok cok -> tryParses f err eok cok
    ConsumedFail err -> ConsumedFail err
    EmptyFail err -> EmptyFail err

#ifdef __GHCJS__
  fail s = Parser $ \st ->
    EmptyFail $ newErrorMessage (newMessage (Text.pack s)) (stPosition st)
#endif

instance Fail.MonadFail (Parser st) where
  fail s = Parser $ \st ->
    EmptyFail $ newErrorMessage (newMessage (Text.pack s)) (stPosition st)

-- This function is simple, but unfriendly to read because of all the
-- accumulators involved. A clearer definition would be welcome.
tryParses :: forall a b st. (a -> Parser st b)
  -> ParseError -> [ParseResult st a] -> [ParseResult st a]
  -> ParseOut st b
tryParses f err = go err [] [] [] []
  where
    -- The reverses are just for debugging to force an intuitive order.
    -- They are not necessary.
    go :: ParseError
      -> [ParseResult st b]
      -> [ParseResult st b]
      -> [ParseError]
      -> [ParseError]
      -> [ParseResult st a]
      -> [ParseResult st a]
      -> ParseOut st b
    go accErr accEmptyOk accConsumedOk accConsumedFails accEmptyFails emptyOks consumedOks =
      case (emptyOks, consumedOks) of

      -- If we have no further input: exit based on the accumulated results
      ([],[]) -> if
        | not $ null (accEmptyOk ++ accConsumedOk) -> Continuation accErr (reverse accEmptyOk) (reverse accConsumedOk)
        | not $ null accEmptyFails -> EmptyFail $ foldl' (<>) err $ accEmptyFails ++ accConsumedFails
        | not $ null accConsumedFails -> ConsumedFail $ foldl' (<>) err $ accConsumedFails
        | otherwise -> error "tryParses: parser has empty result"

      -- If we have further input first work on the 'emptyOk' results
      ((PR a st):rs, ys) -> case runParser (f a) st of
        Continuation ferr feok fcok ->
            go (accErr <> ferr) (reverse feok ++ accEmptyOk) (reverse fcok ++ accConsumedOk) accConsumedFails accEmptyFails rs ys
        ConsumedFail err' -> go accErr accEmptyOk accConsumedOk (err':accConsumedFails) accEmptyFails rs ys
        EmptyFail err' -> go accErr accEmptyOk accConsumedOk accConsumedFails (err':accEmptyFails) rs ys

      -- .. and then on the 'consumerOk' ones.
      ([], (PR a st):rs) -> case runParser (f a) st of
        Continuation ferr feok fcok ->
              go (accErr <+> ferr) accEmptyOk (reverse feok ++ reverse fcok ++ accConsumedOk) accConsumedFails accEmptyFails [] rs
        ConsumedFail err' -> go accErr accEmptyOk accConsumedOk (err':accConsumedFails) accEmptyFails [] rs
        EmptyFail err' -> go accErr accEmptyOk accConsumedOk (err':accConsumedFails) accEmptyFails [] rs

instance Alternative (Parser st) where
  empty = mzero
  (<|>) = mplus

instance MonadPlus (Parser st) where
  mzero = Parser \st -> EmptyFail $ newErrorUnknown (stPosition st)
  (Parser m) `mplus` (Parser n) = Parser $ \st ->
    case m st of
      EmptyFail err -> case n st of
        Continuation err' a b -> Continuation (err <+> err') a b
        ConsumedFail err' -> ConsumedFail (err <+> err')
        EmptyFail err' -> EmptyFail (err <+> err')
      c -> c

-- Escaping the parser

-- | Reply type
data Reply a
  = Ok [a]
  | Error ParseError
  deriving (Eq, Show)


-- | Running the parser
runP :: Parser st a -> State st -> Reply (ParseResult st a)
runP (Parser p) st = case p st of
  Continuation _ emptyOk consumedOk -> Ok (emptyOk ++ consumedOk)
  ConsumedFail err -> Error err
  EmptyFail err -> Error err

-- Parser state management

-- | Manage user state.
instance MonadState st (Parser st) where

  get :: Parser st st
  get = Parser \st ->
    Continuation (newErrorUnknown (stPosition st)) [PR (stUser st) st] []

  put :: st -> Parser st ()
  put s = Parser \st ->
    Continuation (newErrorUnknown (stPosition st)) [PR () st {stUser = s}] []

-- | Get the @stInput@ as a @ParseResult@.
getInput :: Parser st [Token]
getInput = Parser \st ->
  Continuation (newErrorUnknown (stPosition st)) [PR (stInput st) st] []

-- | Get the @stPosition@ as a @ParseResult@.
getPos :: Parser st SourcePos
getPos = Parser \st ->
  Continuation (newErrorUnknown (stPosition st)) [PR (stPosition st) st] []

-- | Get the tokens before the current @stPosition@ as a @ParseResult@.
getTokens :: [Token] -> Parser st [Token]
getTokens inp = Parser \st ->
  let pos = stPosition st
      toks = takeWhile (\tok -> tokenPos tok < pos) inp -- TODO: Don't use the default Ord instance
  in  Continuation (newErrorUnknown (stPosition st)) [PR toks st] []
