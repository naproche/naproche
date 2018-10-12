{-
Authors: Steffen Frerix (2017 - 2018)

Parser combinators.
-}

module Alice.Parser.Combinators where

import Alice.Parser.Base
import Alice.Parser.Token
import Alice.Parser.Error

import Data.Char
import Data.List

import Control.Monad
import Data.Maybe (isJust, fromJust)
import Debug.Trace


--- ambiguity parsing combinators



sepBy :: Parser st a -> Parser st sep -> Parser st [a]
sepBy p sep = liftM2 (:) p $ opt [] $ sep >> sepBy p sep


sepByLL1 :: Parser st a -> Parser st sep -> Parser st [a]
sepByLL1 p sep = liftM2 (:) p $ optLL1 [] $ sep >> sepByLL1 p sep

-- option deciding in LL1 fashion
optLL1 :: a -> Parser st a -> Parser st a
optLL1 x p = p <|> return x

optLLx :: a -> Parser st a -> Parser st a
optLLx x p = p </> return x

opt :: a -> Parser st a -> Parser st a
opt x p = p -|- return x

chain :: Parser st a -> Parser st [a]
chain p = liftM2 (:) p $ opt [] $ chain p

chainLL1 :: Parser st a -> Parser st [a]
chainLL1 p = liftM2 (:) p $ optLL1 [] $ chainLL1 p


satisfy :: (String -> Bool) -> Parser st String
satisfy pr = tokenPrim prTest
  where
    prTest tk = let s = showToken tk in guard (pr s) >> return s

after :: Parser st a -> Parser st b -> Parser st a
after a b = a >>= ((b >>) . return)


-- brackets and parentheses

expar p = wd_token "(" >> after p (wd_token ")")
exbrk p = wd_token "[" >> after p (wd_token "]")
exbrc p = wd_token "{" >> after p (wd_token "}")
paren p = p -|- expar p

dot p = after p $ (wd_token "." <?> "a dot")

narrow :: Show a => Parser st a -> Parser st a
narrow p = Parser $ \st ok cerr eerr ->
  let pok err eok cok = case eok ++ cok of
        [_] -> ok err eok cok
        ls  ->  eerr $ newErrorMessage (newWfMsg ["ambiguity error" ++ show (map prResult ls)]) (stPosi st)
  in  runParser p st pok cerr eerr


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
      case compare (stPosi . prState $ l) (stPosi . prState $ c) of
        GT -> lng (l:ls) cs
        LT -> lng [c] cs
        EQ -> lng (c:l:ls) cs

---- some macros

word = satisfy $ \tk -> all isAlpha tk

wd_token :: String -> Parser st ()
wd_token s = void $ satisfy $ \tk -> s == map toLower tk
wd_tokenOf :: [String] -> Parser st ()
wd_tokenOf ls = void $ satisfy $ \tk -> map toLower tk `elem` ls

sm_token :: String -> Parser st ()
sm_token s = void $ satisfy $ \tk -> s == tk

symbol :: String -> Parser st ()
symbol []     = return ()
symbol (c:cs) = sm_token [c] >> symbol cs




anyToken = tokenPrim (Just . showToken)


eof :: Parser st ()
eof = label "end of input" $ Parser $ \st ok cerr eerr ->
  let inp = stInput st; t = head inp
  in  if null inp
      then ok (unknownError st) [PR () st] []
      else eerr $ unexpectError (showToken t) (tokenPos t)


noError :: Parser st a -> Parser st a
noError p = Parser $ \st ok cerr eerr ->
  let pok   err = ok   $ unknownError st
      pcerr err = cerr $ unknownError st
      peerr err = eerr $ unknownError st
  in  runParser p st pok pcerr peerr



unexpectedUnit :: Parser st a -> Parser st a
unexpectedUnit p = Parser $ \st ok cerr eerr ->
  let pcerr err = cerr $ unexpectError (unit err st) (stPosi st)
      peerr err = eerr $ unexpectError (unit err st) (stPosi st)
  in  runParser p st ok pcerr peerr
  where
    unit err =
      let pos = errorPos err
      in  unwords . map showToken . takeWhile ((>=) pos . tokenPos) . stInput

lexicalCheck :: (a -> Bool) -> Parser st a -> Parser st a
lexicalCheck check p = Parser $ \st ok cerr eerr ->
  let pok err eok cok =
        let wfEok = filter (check . prResult) eok
            wfCok = filter (check . prResult) cok
        in  if null $ wfEok ++ wfCok
            then eerr $ unexpectError (unit err st) (stPosi st)
            else ok err wfEok wfCok
  in  runParser p st pok cerr eerr
  where
    unit err =
      let pos = errorPos err
      in  unwords . map showToken . takeWhile ((>=) pos . tokenPos) . stInput

wellFormedCheck :: (a -> Maybe String) -> Parser st a -> Parser st a
wellFormedCheck check p = Parser $ \st ok cerr eerr ->
  let pos = stPosi st
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


-- Debugging


errorTrace :: String -> (ParseResult st a -> String) -> Parser st a -> Parser st a
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
