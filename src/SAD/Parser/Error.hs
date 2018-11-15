{-
Authors: Steffen Frerix (2017 - 2018)

Message and Parse Error data type and core functions.
-}


module SAD.Parser.Error
  ( ParseError,
    errorPos,
    newErrorMessage,
    newErrorUnknown,
    (<+>),
    (<++>),
    setExpectMessage,
    unexpectError,
    newMessage,
    newUnExpect,
    newExpect,
    newWfMsg )
  where
    
import SAD.Core.SourcePos

import Data.List (nub, sort)
import Debug.Trace


data Message
  = ExpectMsg {unExpect :: String, expect :: [String], message :: [String]}
  | WfMsg {message :: [String]} -- Well-formedness message
  | Unknown deriving Show

isUnknownMsg Unknown     = True; isUnknownMsg _ = False
isExpectMsg  ExpectMsg{} = True; isExpectMsg  _ = False
isWfMsg      WfMsg{}     = True; isWfMsg      _ = False

newMessage  msg = ExpectMsg {unExpect = "" , expect = []   , message = [msg]}
newUnExpect tok = ExpectMsg {unExpect = tok, expect = []   , message = []   }
newExpect   msg = ExpectMsg {unExpect = "" , expect = [msg], message = []   }

newWfMsg msgs = WfMsg msgs

instance Enum Message where
  fromEnum Unknown     = 0
  fromEnum ExpectMsg{} = 1
  fromEnum WfMsg{}     = 2
  toEnum _ = error "toEnum is undefined for Message"

instance Eq Message where
  msg1 == msg2 = case compare msg1 msg2 of EQ -> True; _ -> False

instance Ord Message where
  compare msg1 msg2 =
    case compare (fromEnum msg1) (fromEnum msg2) of
      GT -> GT
      LT -> LT
      EQ -> case msg1 of
              ExpectMsg{} -> compare (unExpect msg1) (unExpect msg2)
              _           -> EQ

mergeMessage :: Message -> Message -> Message
mergeMessage msg1 msg2 =
  case compare msg1 msg2 of
    GT -> msg1
    LT -> msg2
    EQ -> mergeM msg1
  where
    mergeM ExpectMsg{} = msg1 {expect  = expect  msg1 ++ expect  msg2,
                               message = message msg1 ++ message msg2}
    mergeM WfMsg{}     = msg1 {message = message msg1 ++ message msg2}
    mergeM _           = msg1


data ParseError = ParseError {pePos :: SourcePos, peMsg :: Message} deriving Eq


instance Ord ParseError where
  compare (ParseError pos1 msg1) (ParseError pos2 msg2)
    | isWfMsg msg1 = if isWfMsg msg2 then compare pos1 pos2 else GT
    | isWfMsg msg2 = if isWfMsg msg1 then compare pos1 pos2 else LT
    | otherwise    = compare pos1 pos2


errorPos :: ParseError -> SourcePos
errorPos (ParseError pos _) = pos

newErrorMessage :: Message -> SourcePos -> ParseError
newErrorMessage msg pos = ParseError pos msg

newErrorUnknown :: SourcePos -> ParseError
newErrorUnknown pos
  = ParseError pos Unknown

mostImportantMerge :: ParseError -> ParseError ->  ParseError
mostImportantMerge e1 e2 = case compare e1 e2 of
       EQ -> e1 {peMsg = mergeMessage (peMsg e1) (peMsg e2)}
       GT -> e1
       LT -> e2


firstSetMerge :: ParseError -> ParseError -> ParseError
firstSetMerge e1@(ParseError pos1 msg1) e2@(ParseError pos2 msg2) =
  case compare pos1 pos2 of
    GT -> e1
    LT -> e2
    EQ | isExpectMsg msg1 -> if   isExpectMsg msg2
                             then e1 {peMsg = mergeMessage msg1 msg2}
                             else e1
       | isExpectMsg msg2 -> e2
       | otherwise        -> e1 {peMsg = mergeMessage msg1 msg2}

(<+>) = firstSetMerge


(<++>) = mostImportantMerge

setExpectMessage :: String -> ParseError -> ParseError
setExpectMessage exp pe@(ParseError pos msg)
  | isUnknownMsg msg = ParseError pos $ newExpect exp
  | isWfMsg      msg = pe
  | otherwise        = ParseError pos $ msg {expect = [exp]}

unexpectError :: String -> SourcePos -> ParseError
unexpectError uex pos = newErrorMessage (newUnExpect uex) pos

errorMessage :: ParseError -> Message
errorMessage (ParseError _ msg) = msg



instance Show ParseError where
    show err
        = show (errorPos err) ++ ":" ++
          showErrorMessage "or" "unknown parse error"
                            "expecting" "unexpected"
                           (errorMessage err)


showErrorMessage :: String -> String -> String -> String -> Message -> String
showErrorMessage msgOr msgUnknown msgExpecting msgUnExpected msg
  | isUnknownMsg msg = msgUnknown
  | isWfMsg      msg = '\n': (showMany "" $ message msg)
  | otherwise = concat $ map ("\n"++) $ clean $
      [showUnExpect,showExpect,showMessages]
  where
    unExpected = unExpect msg
    expected   = expect   msg
    messages   = message  msg

    showExpect   | not (null messages) = ""
                 | otherwise = showMany msgExpecting expected
    showUnExpect | not (null messages) = ""
                 | otherwise = msgUnExpected ++ " " ++ unExpected

    showMessages      = showMany "" messages

    -- helpers
    showMany pre msgs =
      case clean msgs of
        [] -> ""
        ms | null pre  -> commasOr ms
           | otherwise -> pre ++ " " ++ commasOr ms

    commasOr []  = ""
    commasOr [m] = m
    commasOr ms  = commaSep (init ms) ++ " " ++ msgOr ++ " " ++ last ms

    commaSep = separate ", " . clean

    separate   _ []     = ""
    separate   _ [m]    = m
    separate sep (m:ms) = m ++ sep ++ separate sep ms

    clean = nub . filter (not . null)
