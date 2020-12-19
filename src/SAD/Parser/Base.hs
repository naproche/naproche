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

module SAD.Parser.Base
  ( ParserKind(Tex, NonTex),
    Parser(..),
    Continuation,
    EmptyFail,
    ConsumedFail,
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
import SAD.Helpers (notNull)

import SAD.Parser.Token
import SAD.Parser.Error
import SAD.Core.SourcePos

import Data.List
import qualified Data.Text.Lazy as Text


-- | Indicate which of the parsers is currently used. This is must be recorded in the State
-- for read instruction to work properly.
data ParserKind = NonTex | Tex deriving (Eq, Ord, Show)

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

-- | Continutation passing style ambiguity parser
-- In practice: @st@ = @FState@, @r@ = @ParseResult FState a@

type Continuation r st a =
  ParseError -> [ParseResult st a] -> [ParseResult st a] -> r
type EmptyFail    r = ParseError -> r
type ConsumedFail r = ParseError -> r


newtype Parser st a = Parser {runParser :: forall r .
     State st
  -> Continuation r st a
  -> ConsumedFail r
  -> EmptyFail r
  -> r }

instance Functor (Parser st) where
  fmap f p = Parser \ st ok consumedFail err ->
    runParser p st (new ok) consumedFail err
    where
      new ok err emptyOk consumedOk = ok err (map (fmap f) emptyOk) (map (fmap f) consumedOk)

instance Applicative (Parser st) where
  pure = return
  (<*>) = ap

instance Monad (Parser st) where
  return x = Parser \st ok _ _ ->
      ok (newErrorUnknown (stPosition st)) [PR x st] []

  p >>= f = Parser \st ok consumedFail emptyFail ->
    let pok = tryParses f ok consumedFail emptyFail
    in  runParser p st pok consumedFail emptyFail

  fail = Fail.fail

instance Fail.MonadFail (Parser st) where
  fail s = Parser \st _ _ emptyFail ->
    emptyFail $ newErrorMessage (newMessage (Text.pack s)) (stPosition st)



-- This function is simple, but unfriendly to read because of all the
-- accumulators involved. A clearer definition would be welcome.
tryParses :: forall r a b st. (a -> Parser st b)
  -> Continuation r st b
  -> ConsumedFail r
  -> EmptyFail r
  -> Continuation r st a
tryParses f ok consumedFail emptyFail err = go err [] [] [] []
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
      -> r
    go accErr accEmptyOk accConsumedOk accConsumedFails accEmptyFails emptyOks consumedOks =
      case (emptyOks, consumedOks) of

      -- If we have no further input: exit based on the accumulated results
      ([],[]) -> if
        | notNull (accEmptyOk ++ accConsumedOk) -> ok accErr (reverse accEmptyOk) (reverse accConsumedOk)
        | notNull accEmptyFails -> emptyFail $ foldl' (<>) err $ accEmptyFails ++ accConsumedFails
        | notNull accConsumedFails -> consumedFail $ foldl' (<>) err $ accConsumedFails
        | otherwise -> error "tryParses: parser has empty result"

      -- If we have further input first work on the 'emptyOk' results
      ((PR a st):rs, ys) ->
        let fok ferr feok fcok =
              go (accErr <> ferr) (reverse feok ++ accEmptyOk) (reverse fcok ++ accConsumedOk) accConsumedFails accEmptyFails rs ys
            fcerr err' = go accErr accEmptyOk accConsumedOk (err':accConsumedFails) accEmptyFails rs ys
            feerr err' = go accErr accEmptyOk accConsumedOk accConsumedFails (err':accEmptyFails) rs ys
        in  runParser (f a) st fok fcerr feerr

      -- .. and then on the 'consumerOk' ones.
      ([], (PR a st):rs) ->
        let fok ferr feok fcok =
              go (accErr <+> ferr) accEmptyOk (reverse feok ++ reverse fcok ++ accConsumedOk) accConsumedFails accEmptyFails [] rs
            fcerr err' = go accErr accEmptyOk accConsumedOk (err':accConsumedFails) accEmptyFails [] rs
            feerr err' = go accErr accEmptyOk accConsumedOk (err':accConsumedFails) accEmptyFails [] rs
        in  runParser (f a) st fok fcerr feerr


instance Alternative (Parser st) where
  empty = mzero
  (<|>) = mplus


instance MonadPlus (Parser st) where
  mzero = Parser \st _ _ emptyFail -> emptyFail $ newErrorUnknown (stPosition st)
  m `mplus` n = Parser \st ok consumedFail emptyFail ->
    let meerr err =
          let nok   err' = ok (err <+> err')
              ncerr err' = consumedFail (err <> err')
              neerr err' = emptyFail (err <> err')
          in  runParser n st nok ncerr neerr
    in  runParser m st ok consumedFail meerr



-- Escaping the parser

-- | Reply type
data Reply a
  = Ok [a]
  | Error ParseError
  deriving (Eq, Show)


-- | Running the parser
runP :: Parser st a -> State st -> Reply (ParseResult st a)
runP p st = runParser p st ok consumedFail emptyFail
  where
    ok _ emptyOk consumedOk = Ok (emptyOk ++ consumedOk)
    consumedFail err  = Error err
    emptyFail err     = Error err


-- Parser state management

-- | Manage user state.
instance MonadState st (Parser st) where

  get :: Parser st st
  get = Parser \st ok _consumedFail _emptyFail ->
    ok (newErrorUnknown (stPosition st)) [PR (stUser st) st] []

  put :: st -> Parser st ()
  put s = Parser \st ok _consumedFail _emptyFail ->
    ok (newErrorUnknown (stPosition st)) [PR () st {stUser = s}] []


-- | Get the @stInput@ as a @ParseResult@.
getInput :: Parser st [Token]
getInput = Parser \st ok _ _ ->
  ok (newErrorUnknown (stPosition st)) [PR (stInput st) st] []

-- | Get the @stPosition@ as a @ParseResult@.
getPos :: Parser st SourcePos
getPos = Parser \st ok _ _ ->
  ok (newErrorUnknown (stPosition st)) [PR (stPosition st) st] []

-- | Get the tokens before the current @stPosition@ as a @ParseResult@.
getTokens :: [Token] -> Parser st [Token]
getTokens inp = Parser \st ok _ _ ->
  let pos = stPosition st
      toks = takeWhile (\tok -> tokenPos tok < pos) inp -- TODO: Don't use the default Ord instance
  in  ok (newErrorUnknown (stPosition st)) [PR toks st] []
