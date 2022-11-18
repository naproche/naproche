-- |
-- Authors: Steffen Frerix (2017 - 2018)
--
-- Message and Parse Error data type and core functions.


{-# LANGUAGE OverloadedStrings #-}

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

import Data.List (intercalate)
import Data.Ord (comparing)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

import SAD.Helpers (notNull, nubOrd)
import SAD.Core.Message (show_position)

import qualified Isabelle.Position as Position


data Message
  = ExpectMsg {unexpect :: Text, expect :: [Text], message :: [Text]}
  | WellFormednessMessage {message :: [Text]}
  | Unknown
  deriving (Eq, Ord, Show)

isUnknownMsg, isExpectMsg, isWellFormednessMessage :: Message -> Bool
isUnknownMsg Unknown = True
isUnknownMsg _ = False
isExpectMsg ExpectMsg{} = True
isExpectMsg _ = False
isWellFormednessMessage WellFormednessMessage{} = True
isWellFormednessMessage _ = False

newMessage, newUnexpect, newExpect :: Text -> Message
newMessage  msg = ExpectMsg {unexpect = "" , expect = []   , message = [msg]}
newUnexpect tok = ExpectMsg {unexpect = tok, expect = []   , message = []   }
newExpect   msg = ExpectMsg {unexpect = "" , expect = [msg], message = []   }

newWellFormednessMessage :: [Text] -> Message
newWellFormednessMessage msgs = WellFormednessMessage msgs

compareImportance :: Message -> Message -> Ordering
compareImportance msg1 msg2 =
  case comparing importance msg1 msg2 of
    GT -> GT
    LT -> LT
    EQ -> case msg1 of
      ExpectMsg{} -> comparing unexpect msg1 msg2
      _           -> EQ
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
    deriving (Eq, Ord)

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

setExpectMessage :: Text -> ParseError -> ParseError
setExpectMessage expe pe@(ParseError pos msg)
  | isUnknownMsg msg = ParseError pos $ newExpect expe
  | isWellFormednessMessage      msg = pe
  | otherwise        = ParseError pos $ msg {expect = [expe]}

unexpectError :: Text -> Position.T -> ParseError
unexpectError uex pos = newErrorMessage (newUnexpect uex) pos

errorMessage :: ParseError -> Message
errorMessage (ParseError _ msg) = msg

instance Show ParseError where
  show err = show_position (errorPos err) ++ ":\n"
          ++ showErrorMessage (errorMessage err)

showErrorMessage :: Message -> String
showErrorMessage msg = case msg of
  Unknown -> "unknown parse error"
  WellFormednessMessage m -> commasOr $ clean $ map Text.unpack m
  ExpectMsg unexpected expected msgs -> case clean $ map Text.unpack msgs of
    [] -> unlines $ clean $ ["unexpected " ++ Text.unpack unexpected, showMany "expecting" (clean $ map Text.unpack expected)]
    messages -> commasOr messages
  where
    showMany :: String -> [String] -> String
    showMany "" msgs = commasOr msgs
    showMany _ [] = ""
    showMany pre msgs = pre ++ " " ++ commasOr msgs

    commasOr :: [String] -> String
    commasOr []  = ""
    commasOr [m] = m
    commasOr ms  = intercalate ", " (init ms) ++ " or " ++ last ms

    clean :: [String] -> [String]
    clean = nubOrd . filter notNull
