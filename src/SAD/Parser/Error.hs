{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Parser.Error
-- Description : Message and Parse Error data type and core functions.
-- Copyright   : (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
module SAD.Parser.Error (
  ParseError(..),
  newErrorMessage,
  newErrorUnknown,
  (<+>),
  setExpectMessage,
  unexpectError,
  newMessage,
  newUnexpect,
  newExpect,
  newWellFormednessMessage
) where

import Data.List.Extra (nubOrd)
import Data.Ord (comparing)

import Isabelle.Bytes (Bytes)
import Isabelle.Bytes qualified as Bytes
import Isabelle.Library (commas, implode_space)
import Isabelle.Position qualified as Position

import SAD.Core.Message (console_position)
import SAD.Export.Pretty


data Message
  = ExpectMsg {unexpect :: Bytes, expect :: [Bytes], message :: [Bytes]}
  | WellFormednessMessage {message :: [Bytes]}
  | Unknown

isUnknownMsg, isExpectMsg, isWellFormednessMessage :: Message -> Bool
isUnknownMsg Unknown = True
isUnknownMsg _ = False
isExpectMsg ExpectMsg{} = True
isExpectMsg _ = False
isWellFormednessMessage WellFormednessMessage{} = True
isWellFormednessMessage _ = False

newMessage, newUnexpect, newExpect :: Bytes -> Message
newMessage  msg = ExpectMsg {unexpect = "" , expect = []   , message = [msg]}
newUnexpect tok = ExpectMsg {unexpect = tok, expect = []   , message = []   }
newExpect   msg = ExpectMsg {unexpect = "" , expect = [msg], message = []   }

newWellFormednessMessage :: [Bytes] -> Message
newWellFormednessMessage = WellFormednessMessage

compareImportance :: Message -> Message -> Ordering
compareImportance msg1 msg2 =
  case comparing importance msg1 msg2 of
    GT -> GT
    LT -> LT
    EQ -> case msg1 of
      ExpectMsg{} -> comparing unexpect msg1 msg2
      _ -> EQ
  where
    importance :: Message -> Int
    importance Unknown = 0
    importance ExpectMsg{} = 1
    importance WellFormednessMessage{} = 2

-- | Messages are a 'Semigroup' under importance-biased merging.
instance Semigroup Message where
  (<>) :: Message -> Message -> Message
  msg1 <> msg2 =
    case compareImportance msg1 msg2 of
      GT -> msg1
      LT -> msg2
      EQ -> msg
    where
      msg = case msg1 of
        ExpectMsg{} ->
          msg1 {expect = expect msg1 ++ expect msg2, message = message msg1 ++ message msg2}
        WellFormednessMessage{} ->
          msg1 {message = message msg1 ++ message msg2}
        Unknown -> msg1


data ParseError = ParseError {errorPos :: Position.T, peMsg :: Message}

urgency :: ParseError -> ParseError -> Ordering
urgency (ParseError pos1 msg1) (ParseError pos2 msg2)
  | isWellFormednessMessage msg1 && not (isWellFormednessMessage msg2) = GT
  | isWellFormednessMessage msg2 && not (isWellFormednessMessage msg1) = LT
  | otherwise = compare pos1 pos2

-- | @ParserError@ is a 'Semigroup' under left-biased importance merge.
instance Semigroup ParseError where
  (<>) :: ParseError -> ParseError -> ParseError
  e1 <> e2 = case urgency e1 e2 of
    EQ -> e1 {peMsg = peMsg e1 <> peMsg e2}
    GT -> e1
    LT -> e2

newErrorMessage :: Message -> Position.T -> ParseError
newErrorMessage msg pos = ParseError pos msg

newErrorUnknown :: Position.T -> ParseError
newErrorUnknown pos = ParseError pos Unknown

-- | Left-biased merge based on importance favouring @ExpectMsg@s.
(<+>) :: ParseError -> ParseError -> ParseError
(<+>) e1@(ParseError pos1 msg1) e2@(ParseError pos2 msg2) =
  case compare pos1 pos2 of
    GT -> e1
    LT -> e2
    EQ | isExpectMsg msg1 -> if   isExpectMsg msg2
                             then e1 {peMsg = msg1 <> msg2}
                             else e1
       | isExpectMsg msg2 -> e2
       | otherwise        -> e1 {peMsg = msg1 <> msg2}

setExpectMessage :: Bytes -> ParseError -> ParseError
setExpectMessage expe pe@(ParseError pos msg)
  | isUnknownMsg msg = ParseError pos $ newExpect expe
  | isWellFormednessMessage      msg = pe
  | otherwise        = ParseError pos $ msg {expect = [expe]}

unexpectError :: Bytes -> Position.T -> ParseError
unexpectError uex = newErrorMessage (newUnexpect uex)

errorMessage :: ParseError -> Message
errorMessage (ParseError _ msg) = msg

instance Pretty ParseError where
  pretty_print err = console_position (errorPos err) <> ":\n"
          <> showErrorMessage (errorMessage err)

showErrorMessage :: Message -> Bytes
showErrorMessage msg = case msg of
  Unknown -> "unknown parse error"
  WellFormednessMessage m -> commasOr $ clean m
  ExpectMsg unexpected expected msgs -> case clean msgs of
    [] -> implode_space $ clean ["Unexpected \"" <> unexpected <> "\".", showMany "Expecting" (clean expected) <> "."]
    messages -> commasOr messages
  where
    showMany :: Bytes -> [Bytes] -> Bytes
    showMany "" msgs = commasOr msgs
    showMany _ [] = ""
    showMany pre msgs = pre <> " " <> commasOr msgs

    commasOr :: [Bytes] -> Bytes
    commasOr [] = ""
    commasOr [m] = m
    commasOr ms = commas (init ms) <> " or " <> last ms

    clean :: [Bytes] -> [Bytes]
    clean = nubOrd . filter (not . Bytes.null)
