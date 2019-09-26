{-
Authors: Steffen Frerix (2017 - 2018)

Message and Parse Error data type and core functions.
-}

{-# OPTIONS_GHC -Wall -fno-warn-unused-do-bind #-}

module SAD.Parser.Error
  ( ParseError(..),
    newErrorMessage,
    newErrorUnknown,
    (<+>),
    (<++>),
    setExpectMessage,
    unexpectError,
    newMessage,
    newUnExpect,
    newExpect,
    newWellFormednessMessage )
  where

import SAD.Core.SourcePos
import SAD.Helpers (nubOrd)
import Data.List

data Message
  = ExpectMsg {unExpect :: String, expect :: [String], message :: [String]}
  | WellFormednessMessage {message :: [String]}
  | Unknown 
  deriving (Eq, Ord, Show)

isUnknownMsg, isExpectMsg, isWellFormednessMessage :: Message -> Bool
isUnknownMsg Unknown = True
isUnknownMsg _ = False
isExpectMsg ExpectMsg{} = True
isExpectMsg _ = False
isWellFormednessMessage WellFormednessMessage{} = True
isWellFormednessMessage _ = False

newMessage, newUnExpect, newExpect :: String -> Message
newMessage  msg = ExpectMsg {unExpect = "" , expect = []   , message = [msg]}
newUnExpect tok = ExpectMsg {unExpect = tok, expect = []   , message = []   }
newExpect   msg = ExpectMsg {unExpect = "" , expect = [msg], message = []   }

newWellFormednessMessage :: [String] -> Message
newWellFormednessMessage msgs = WellFormednessMessage msgs

compareImportance :: Message -> Message -> Ordering
compareImportance msg1 msg2 = 
    case compare (numerate msg1) (numerate msg2) of
      GT -> GT
      LT -> LT
      EQ -> case msg1 of
              ExpectMsg{} -> compare (unExpect msg1) (unExpect msg2)
              _           -> EQ
    where
      numerate :: Message -> Int
      numerate Unknown     = 0
      numerate ExpectMsg{} = 1
      numerate WellFormednessMessage{}     = 2

mergeMessage :: Message -> Message -> Message
mergeMessage msg1 msg2 =
  case compareImportance msg1 msg2 of
    GT -> msg1
    LT -> msg2
    EQ -> mergeM msg1
  where
    mergeM ExpectMsg{} = msg1 {expect  = expect  msg1 ++ expect  msg2,
                               message = message msg1 ++ message msg2}
    mergeM WellFormednessMessage{}     = msg1 {message = message msg1 ++ message msg2}
    mergeM _           = msg1


data ParseError = ParseError {errorPos :: SourcePos, peMsg :: Message}

-- TODO: There are ParseErrors p1, p2 with p1 == p2, but compare p1 p2 /= EQ
instance Eq ParseError where
  (ParseError p1 m1) == (ParseError p2 m2) = p1 == p2 && compareImportance m1 m2 == EQ

instance Ord ParseError where
  compare (ParseError pos1 msg1) (ParseError pos2 msg2)
    | isWellFormednessMessage msg1 = if isWellFormednessMessage msg2 then compare pos1 pos2 else GT
    | isWellFormednessMessage msg2 = if isWellFormednessMessage msg1 then compare pos1 pos2 else LT
    | otherwise    = compare pos1 pos2


newErrorMessage :: Message -> SourcePos -> ParseError
newErrorMessage msg pos = ParseError pos msg

newErrorUnknown :: SourcePos -> ParseError
newErrorUnknown pos = ParseError pos Unknown

-- | Left-biased merge based on importance favouring @ExpectMsg@s.
(<+>) :: ParseError -> ParseError -> ParseError
(<+>) e1@(ParseError pos1 msg1) e2@(ParseError pos2 msg2) =
  case compare pos1 pos2 of
    GT -> e1
    LT -> e2
    EQ | isExpectMsg msg1 -> if   isExpectMsg msg2
                             then e1 {peMsg = mergeMessage msg1 msg2}
                             else e1
       | isExpectMsg msg2 -> e2
       | otherwise        -> e1 {peMsg = mergeMessage msg1 msg2}

-- | Left-biased merge based on importance.
(<++>) :: ParseError -> ParseError -> ParseError
e1 <++> e2 = case compare e1 e2 of
       EQ -> e1 {peMsg = mergeMessage (peMsg e1) (peMsg e2)}
       GT -> e1
       LT -> e2

setExpectMessage :: String -> ParseError -> ParseError
setExpectMessage expe pe@(ParseError pos msg)
  | isUnknownMsg msg = ParseError pos $ newExpect expe
  | isWellFormednessMessage      msg = pe
  | otherwise        = ParseError pos $ msg {expect = [expe]}

unexpectError :: String -> SourcePos -> ParseError
unexpectError uex pos = newErrorMessage (newUnExpect uex) pos

errorMessage :: ParseError -> Message
errorMessage (ParseError _ msg) = msg

instance Show ParseError where
    show err = show (errorPos err) ++ ":\n"
            ++ showErrorMessage (errorMessage err)

showErrorMessage :: Message -> String
showErrorMessage msg = case msg of
  Unknown -> "unknown parse error"
  WellFormednessMessage m -> commasOr $ clean m
  ExpectMsg unExpected expected msgs -> case clean msgs of
    [] -> unlines $ clean $ ["unexpected " ++ unExpected, showMany "expecting" (clean expected)]
    messages -> commasOr messages
  where
    showMany :: String -> [String] -> String
    showMany [] msgs = commasOr msgs
    showMany _ [] = ""
    showMany pre msgs = pre ++ " " ++ commasOr msgs

    commasOr :: [String] -> String
    commasOr []  = ""
    commasOr [m] = m
    commasOr ms  = intercalate ", " (init ms) ++ " or " ++ last ms

    clean :: [String] -> [String]
    clean = nubOrd . filter (not . null)
