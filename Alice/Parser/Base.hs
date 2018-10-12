{-
Authors: Steffen Frerix (2017 - 2018)

Parser datatype and monad instance.
-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Alice.Parser.Base where

import Control.Monad
import qualified Control.Applicative as Applicative
import Control.Monad.State.Class


import Alice.Parser.Token
import Alice.Parser.Error
import Alice.Parser.Position

import Data.Char
import Data.List

import Debug.Trace

--- Ambiguous Reply processing
data Reply a = Ok [a] | Error ParseError deriving Show




data State st = State {stUser :: st, stInput :: [Token] } deriving Show

stPosi :: State st -> SourcePos
stPosi (State _ (t:ts)) = tokenPos t
stPosi (State _ [])     = EOF


showCurrentToken st = case stInput st of
  (t:ts) -> showToken t
  _      -> "end of input"

data ParseResult st a = PR { prResult :: a, prState :: State st } deriving Show


instance Functor (ParseResult a) where
  fmap f p@PR{prResult = a} = p {prResult = f a}


type Continuation st a b =
  ParseError -> [ParseResult st a] -> [ParseResult st a] -> b
type EmptyFail b = ParseError -> b
type ConsumedFail b = ParseError -> b

--- Ambiguity Parser


newtype Parser st a = Parser {runParser :: forall b .
     State st
  -> Continuation st a b -- consumed ok, first argument is emptyOk, second argument is consumedOk
  -> ConsumedFail b                -- comsumed error
  -> EmptyFail b                  -- empty error
  -> b }


runP :: Parser st a -> State st -> Reply (ParseResult st a)
runP p st = runParser p st ok cerr eerr
  where
    ok _ eok cok = Ok $ eok ++ cok
    cerr err     = Error err
    eerr err     = Error err

instance Functor (Parser st) where
  fmap f p = Parser $ \ st ok cerr err ->
    runParser p st (new ok) cerr err
    where
      new ok err eok cok = ok err (map (fmap f) eok) (map (fmap f) cok)

instance Monad (Parser st) where
  return x = Parser $ \st ok _ _ ->
      ok (unknownError st) [PR x st] []

  p >>= f = Parser $ \st ok cerr eerr ->
    let pok = tryParses f ok cerr eerr
        pcerr = cerr
        peerr = eerr
    in runParser p st pok pcerr peerr

  fail s = Parser $ \st _ _ eerr ->
    eerr $ newErrorMessage (newMessage s) (stPosi st)


-- the reverses are just for debugging to force an intuitive order, but are not necessary at all
tryParses :: (a -> Parser st b) -> Continuation st b c -> ConsumedFail c -> EmptyFail c -> ParseError -> [ParseResult st a] -> [ParseResult st a] ->  c
tryParses f ok cerr eerr err eok cok = accumE err [] [] [] [] eok
  where
    accumE acc_err acc_eok acc_cok acc_cerr acc_eerr ((PR a st'):rs) =
      let fok ferr feok fcok = accumE (acc_err <++> ferr) (reverse feok ++ acc_eok) (reverse fcok ++ acc_cok) acc_cerr acc_eerr rs
          fcerr err'    = accumE acc_err acc_eok acc_cok (err':acc_cerr) acc_eerr rs
          feerr err'    = accumE acc_err acc_eok acc_cok acc_cerr (err':acc_eerr) rs
      in  runParser (f a) st' fok fcerr feerr
    accumE acc_err acc_eok acc_cok acc_cerr acc_eerr [] = accumC acc_err acc_eok acc_cok acc_cerr acc_eerr cok

    accumC acc_err acc_eok acc_cok acc_cerr acc_eerr ((PR a st'):rs) =
      let fok ferr feok fcok = accumC (acc_err <+> ferr) acc_eok (reverse feok ++ reverse fcok ++ acc_cok) acc_cerr acc_eerr rs
          fcerr err'    = accumC acc_err acc_eok acc_cok (err':acc_cerr) acc_eerr rs
          feerr err'    = accumC acc_err acc_eok acc_cok (err':acc_cerr) acc_eerr rs
      in  runParser (f a) st' fok fcerr feerr
    accumC acc_err acc_eok acc_cok acc_cerr acc_eerr []
      | (not $ null acc_eok)  || (not $ null acc_cok)  = ok acc_err (reverse acc_eok) (reverse acc_cok)
      | (not $ null acc_eerr) = eerr $ foldl' (<++>) err $ acc_eerr ++ acc_cerr
      | (not $ null acc_cerr) = cerr $ foldl' (<++>) err $ acc_cerr
      | otherwise = error "tryParses: parser has empty result"




unknownError :: State st -> ParseError
unknownError st = newErrorUnknown (stPosi st)



instance MonadPlus (Parser st) where
  mzero       = Parser $ \st _ _ eerr -> eerr $ unknownError st
  mplus m n = Parser $ \st ok cerr eerr ->
    let meerr err =
          let nok   err' = ok   $ err <+>  err'
              ncerr err' = cerr $ err <++> err'
              neerr err' = eerr $ err <++> err'
          in  runParser n st nok ncerr neerr
    in  runParser m st ok cerr meerr

(<|>) :: Parser st a -> Parser st a -> Parser st a
(<|>) = mplus



(</>) :: Parser st a -> Parser st a -> Parser st a
(</>) f g = try f <|> g

--- standard generalization

instance Applicative.Applicative (Parser st) where
  pure = return
  (<*>) = ap

instance Applicative.Alternative (Parser st) where
  empty = mzero
  (<|>) = mplus

--- Parser primitives




infix 0 <?>
(<?>) :: Parser st a -> String -> Parser st a
p <?> msg = Parser $ \st ok cerr eerr ->
  let pok err   = ok   $ setError (stPosi st) err
      pcerr     = cerr
      peerr err = eerr $ setError (stPosi st) err
  in  runParser p st pok pcerr peerr
  where
    setError pos err =
      if   pos < errorPos err
      then err
      else setExpectMessage msg err

label msg p = p <?> msg


tokenPrim :: (Token -> Maybe a) -> Parser st a
tokenPrim test = Parser $ \(State st input) ok _ eerr ->
  case uncons input of
    Nothing     -> eerr $ unexpectError "" EOF
    Just (t,ts) -> case test t of
      Just x  ->
        let newstate = State st ts
            newpos   = nextPos ts
            newerr   = newErrorUnknown newpos
        in  seq newstate $ ok newerr [] . pure $ PR x newstate
      Nothing -> eerr $ unexpectError (showToken t) (tokenPos t)




(-|-) :: Parser st a -> Parser st a -> Parser st a
(-|-) m n = Parser $ \st ok cerr eerr ->
  let mok err eok cok =
        let nok err' eok' cok' = ok (err <+> err') (eok ++ eok') (cok ++ cok')
            ncerr err'         = ok (err <+> err') eok cok
            neerr err'         = ok (err <+> err') eok cok
        in  runParser n st nok ncerr neerr
      mcerr err =
        let nok err'      = ok   $ err <+>  err'
            ncerr err'    = cerr $ err <++> err'
            neerr err'    = eerr $ err <++> err'
        in  runParser n st nok ncerr neerr
      meerr err =
        let nok err'      = ok   $ err <+>  err'
            neerr err'    = eerr $ err <++> err'
            ncerr err'    = eerr $ err <++> err'
        in  runParser n st nok ncerr neerr
  in  runParser m st mok mcerr meerr




try :: Parser st a -> Parser st a
try p = Parser $ \st ok _ eerr -> runParser p st ok eerr eerr


tryAll :: [Parser st a] -> Parser st a
tryAll [] = mzero
tryAll (p:ps) = p -|- tryAll ps


infixr 2 <|>
infixr 2 -|-


failing :: Parser st a -> Parser st ()
failing p = Parser $ \st ok cerr eerr ->
  let pok err eok _ =
        if   null eok
        then cerr $ unexpectError (showCurrentToken st) (stPosi st)
        else eerr $ unexpectError (showCurrentToken st) (stPosi st)
      peerr _ = ok (unknownError st) [PR () st] []
      pcerr _ = ok (unknownError st) [PR () st] []
  in  runParser p st pok pcerr peerr


failAt :: SourcePos -> String -> Parser st a
failAt pos msg = Parser $ \st _ _ eerr ->
  eerr $ newErrorMessage (newMessage msg) pos


failWF :: String -> Parser st a
failWF msg = Parser $ \st _ _ eerr ->
  eerr $ newErrorMessage (newWfMsg [msg]) (stPosi st)
---- state management

instance MonadState st (Parser st) where
  get   = Parser $ \st ok _ _ -> ok (unknownError st) [PR (stUser st) st] []
  put s =
    Parser $ \st ok cerr eerr -> ok (unknownError st) [PR () st {stUser = s}] []


getInput :: Parser st [Token]
getInput = Parser $ \st@(State _ inp) ok _ _ ->
  ok (unknownError st) [PR inp st] []

getPos :: Parser st SourcePos
getPos = Parser $ \st ok _ _ ->
  ok (unknownError st) [PR (stPosi st) st] []

getText :: [Token] -> Parser st String
getText inp = Parser $ \st ok _ _ ->
  let pos = stPosi st
      txt = composeToken $ takeWhile ( (>) pos . tokenPos ) inp
  in  ok (unknownError st) [PR txt st] []
