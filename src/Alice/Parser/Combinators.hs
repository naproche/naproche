{-
Authors: Steffen Frerix (2017 - 2018)

Parser combinators.
-}

module Alice.Parser.Combinators where

import Alice.Parser.Base
import Alice.Parser.Token
import Alice.Parser.Error
import Alice.Parser.Primitives

import Data.Char
import Data.List

import Control.Monad
import Data.Maybe (isJust, fromJust)
import Debug.Trace



-- choices

---- unambiguous choice

------  Choose in LL1 fashion
infixr 2 <|>
{-# INLINE (<|>) #-}
(<|>) :: Parser st a -> Parser st a -> Parser st a
(<|>) = mplus


------ Choose with lookahead
{-# INLINE (</>) #-}
(</>) :: Parser st a -> Parser st a -> Parser st a
(</>) f g = try f <|> g


try :: Parser st a -> Parser st a
try p = Parser $ \st ok _ eerr -> runParser p st ok eerr eerr


---- ambiguous choice

infixr 2 -|-
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

------ ambigous parsing applied ot a list of parsers
tryAll :: [Parser st a] -> Parser st a
tryAll [] = mzero
tryAll (p:ps) = p -|- tryAll ps




-- chain parsing combinators

sepBy :: Parser st a -> Parser st sep -> Parser st [a]
sepBy p sep = liftM2 (:) p $ opt [] $ sep >> sepBy p sep


sepByLL1 :: Parser st a -> Parser st sep -> Parser st [a]
sepByLL1 p sep = liftM2 (:) p $ optLL1 [] $ sep >> sepByLL1 p sep


opt :: a -> Parser st a -> Parser st a
opt x p = p -|- return x


optLL1 :: a -> Parser st a -> Parser st a
optLL1 x p = p <|> return x


optLLx :: a -> Parser st a -> Parser st a
optLLx x p = p </> return x


chain :: Parser st a -> Parser st [a]
chain p = liftM2 (:) p $ opt [] $ chain p


chainLL1 :: Parser st a -> Parser st [a]
chainLL1 p = liftM2 (:) p $ optLL1 [] $ chainLL1 p



-- before and after parses: parentheses, brackets, braces, dots

after :: Parser st a -> Parser st b -> Parser st a
after a b = a >>= ((b >>) . return)

---- mandatory parentheses, brackets, braces
expar, exbrk, exbrc :: Parser st a -> Parser st a
expar p = wdToken "(" >> after p (wdToken ")")
exbrk p = wdToken "[" >> after p (wdToken "]")
exbrc p = wdToken "{" >> after p (wdToken "}")

---- optional parentheses
paren :: Parser st a -> Parser st a
paren p = p -|- expar p

---- mandatory finishing dot
dot :: Parser st a -> Parser st a
dot p = after p $ (wdToken "." <?> "a dot")


-- Control ambiguity

---- if p is ambiguos, fail and report a well-formedness error
narrow :: Show a => Parser st a -> Parser st a
narrow p = Parser $ \st ok cerr eerr ->
  let pok err eok cok = case eok ++ cok of
        [_] -> ok err eok cok
        ls  ->  eerr $ newErrorMessage (newWfMsg ["ambiguity error" ++ show (map prResult ls)]) (stPosition st)
  in  runParser p st pok cerr eerr


---- only take the longest possible parse, discard all others
takeLongest :: Parser st a -> Parser st a
takeLongest p = Parser $ \st ok cerr eerr ->
  let pok err eok cok
        | null cok  = ok err (longest eok) []
        | otherwise = ok err [] (longest cok)
  in  runParser p st pok cerr eerr
  where
    longest = lng []
    lng ls []          = reverse ls
    lng [] (c:cs)      = lng [c] cs
    lng (l:ls) (c:cs) =
      case compare (stPosition . prState $ l) (stPosition . prState $ c) of
        GT -> lng (l:ls) cs
        LT -> lng [c] cs
        EQ -> lng (c:l:ls) cs



-- Deny parses

---- fail if p succeeds
failing :: Parser st a -> Parser st ()
failing p = Parser $ \st ok cerr eerr ->
  let pok err eok _ =
        if   null eok
        then cerr $ unexpectError (showCurrentToken st) (stPosition st)
        else eerr $ unexpectError (showCurrentToken st) (stPosition st)
      peerr _ = ok (newErrorUnknown (stPosition st)) [PR () st] []
      pcerr _ = ok (newErrorUnknown (stPosition st)) [PR () st] []
  in  runParser p st pok pcerr peerr
  where
    showCurrentToken st = case stInput st of
      (t:ts) -> showToken t
      _      -> "end of input"



-- labeling of production rules

infix 0 <?>
(<?>) :: Parser st a -> String -> Parser st a
p <?> msg = Parser $ \st ok cerr eerr ->
  let pok err   = ok   $ setError (stPosition st) err
      pcerr     = cerr
      peerr err = eerr $ setError (stPosition st) err
  in  runParser p st pok pcerr peerr
  where
    setError pos err =
      if   pos < errorPos err
      then err
      else setExpectMessage msg err

label :: String -> Parser st a -> Parser st a
label msg p = p <?> msg



-- Control error messages

---- fail with a well-formedness error
failWF :: String -> Parser st a
failWF msg = Parser $ \st _ _ eerr ->
  eerr $ newErrorMessage (newWfMsg [msg]) (stPosition st)


---- do not produce an error message
noError :: Parser st a -> Parser st a
noError p = Parser $ \st ok cerr eerr ->
  let pok   err = ok   $ newErrorUnknown (stPosition st)
      pcerr err = cerr $ newErrorUnknown (stPosition st)
      peerr err = eerr $ newErrorUnknown (stPosition st)
  in  runParser p st pok pcerr peerr


---- parse and perform a well-formedness check on the result
wellFormedCheck :: (a -> Maybe String) -> Parser st a -> Parser st a
wellFormedCheck check p = Parser $ \st ok cerr eerr ->
  let pos = stPosition st
      pok err eok cok =
        let wfEok = wf eok; wfCok = wf cok
        in  if   null $ wfEok ++ wfCok
            then notWf err eok cok
            else ok err wfEok wfCok
      notWf err eok cok =
        eerr $ newErrorMessage (newWfMsg $ nwf $ eok ++ cok) pos
  in  runParser p st pok cerr eerr
  where
    wf  = filter (not . isJust . check . prResult)
    nwf = map fromJust . filter isJust . map (check . prResult)



---- parse and perform a check on the result; report errors as normal errors
---- and not as well-formedness errors
lexicalCheck :: (a -> Bool) -> Parser st a -> Parser st a
lexicalCheck check p = Parser $ \st ok cerr eerr ->
  let pok err eok cok =
        let wfEok = filter (check . prResult) eok
            wfCok = filter (check . prResult) cok
        in  if null $ wfEok ++ wfCok
            then eerr $ unexpectError (unit err st) (stPosition st)
            else ok err wfEok wfCok
  in  runParser p st pok cerr eerr
  where
    unit err =
      let pos = errorPos err
      in  unwords . map showToken . takeWhile ((>=) pos . tokenPos) . filter (not . isEOF) . stInput


---- in case of failure report every consumed token as unexpected instead of
---- just the first
unexpectedUnit :: Parser st a -> Parser st a
unexpectedUnit p = Parser $ \st ok cerr eerr ->
  let pcerr err = cerr $ unexpectError (unit err st) (stPosition st)
      peerr err = eerr $ unexpectError (unit err st) (stPosition st)
  in  runParser p st ok pcerr peerr
  where
    unit err =
      let pos = errorPos err
      in  unwords . map showToken . takeWhile ((>=) pos . tokenPos) . filter (not . isEOF) . stInput










-- Debugging

---- In case of failure print the error, in case of success print the result
---- of the function shw.
---- This function is implemented using the impure function Debug.Trace.trace
---- and should only be used for debugging purposes.
errorTrace ::
  String -> (ParseResult st a -> String) -> Parser st a -> Parser st a
errorTrace label shw p = Parser $ \st ok cerr eerr ->
    let nok err eok cok = trace (  "error trace (success) : " ++ label ++ "\n"
          ++ tabString ("results (e):\n" ++ tabString (unlines (map shw eok)) )
          ++ tabString ("results (c):\n" ++ tabString (unlines (map shw cok)))
          ++ tabString ("error:\n" ++ tabString (show err))) $ ok err eok cok
        ncerr err = trace ("error trace (consumed): " ++ label ++ "\n" ++  tabString (show err)) $ cerr err
        neerr err = trace ("error trace (empty)   : " ++ label ++ "\n" ++  tabString (show err)) $ eerr err
    in  runParser p st nok ncerr neerr
    where
      tabString = unlines . map ((++) "   ") . lines
