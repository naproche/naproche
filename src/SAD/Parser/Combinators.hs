-- |
-- Module      : SAD.Parser.Combinators
-- Copyright   : (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Parser combinators.


{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Combinators where

import Control.Applicative
import Control.Monad
import Data.Ord (comparing)
import Data.Maybe (isNothing, mapMaybe)
import Debug.Trace
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.Parser.Base
import SAD.Parser.Token
import SAD.Parser.Error
import SAD.Parser.Primitives

import Isabelle.Position qualified as Position


-- * Choices
--
-- $Choices
--
-- To choose in LL1 fashion use '<|>' in @Control.Applicative@

-- | Choose with lookahead.
{-# INLINE (</>) #-}
(</>) :: Parser st a -> Parser st a -> Parser st a
(</>) f g = try f <|> g

-- | Try a parser with lookahead.
try :: Parser st a -> Parser st a
try p = Parser $ \st ok _cerr eerr -> runParser p st ok eerr eerr

-- | Ambiguous choice. Run both parsers and combine the errors and results.
infixr 2 -|-
(-|-) :: forall st a. Parser st a -> Parser st a -> Parser st a
p1 -|- p2 = Parser $ \st ok cerr eerr ->
  let ok1 err eok cok =
        let ok2 err' eok' cok' = ok (err <+> err') (eok ++ eok') (cok ++ cok')
            cerr2 err'         = ok (err <+> err') eok cok
            eerr2 err'         = ok (err <+> err') eok cok
        in  runParser p2 st ok2 cerr2 eerr2
      cerr1 err =
        let ok2 err'      = ok   (err <+>  err')
            cerr2 err'    = cerr (err <> err')
            eerr2 err'    = eerr (err <> err')
        in  runParser p2 st ok2 cerr2 eerr2
      eerr1 err =
        let ok2 err'      = ok   (err <+>  err')
            eerr2 err'    = eerr (err <> err')
            cerr2 err'    = eerr (err <> err')
        in  runParser p2 st ok2 cerr2 eerr2
  in  runParser p1 st ok1 cerr1 eerr1


-- * Chain parsing combinators

-- | Parse @a@s interleaved by @sep@s keeping all intermediary results.
sepBy :: Parser st a -> Parser st sep -> Parser st [a]
sepBy p sep = do
  a <- p
  as <- opt [] $ sep >> sepBy p sep
  pure $ a:as

-- | Same as 'sepBy' but keep only the largest result.
sepByLL1 :: Parser st a -> Parser st sep -> Parser st [a]
sepByLL1 p sep = do
  a <- p
  as <- optLL1 [] $ sep >> sepByLL1 p sep
  pure $ a:as

-- | @opt x p@ runs both @p@ and @x@ and combines their errors and results.
opt :: a -> Parser st a -> Parser st a
opt x p = p -|- return x

-- | @optLL1 x p@ will run @p@; if @p@ fails without consuming any input it will
-- return @x@.
optLL1 :: a -> Parser st a -> Parser st a
optLL1 x p = p <|> return x

-- | @optLLx x p@ will try @p@; if @p@ fails it will return @x@.
optLLx :: a -> Parser st a -> Parser st a
optLLx x p = p </> return x

-- | Run the parser as often as possible keeping all
-- intermediary results.
chain :: Parser st a -> Parser st [a]
chain p = liftM2 (:) p $ opt [] $ chain p

-- | Run the parser as often as possible keeping
-- only the longest result.
chainLL1 :: Parser st a -> Parser st [a]
chainLL1 p = liftM2 (:) p $ optLL1 [] $ chainLL1 p

-- | @after p end@ parses @p@ followed by @end@ and returns the result
-- of @p@. We have @after == (<*)@.
after :: Parser st a -> Parser st b -> Parser st a
after p end = do
  result <- p
  end
  return result

-- | @enclosed begin end p@ parses @begin@, followed by @p@, followed by @end@,
-- returning the result of @p@ and its range.
enclosed :: Text -> Text -> Parser st a -> Parser st (Position.Range, a)
enclosed begin end p = do
  beginPos <- tokenPos' begin
  result <- p
  endPos <- tokenPos' end
  return ((beginPos, endPos), result)


-- * Special combinators for ForTheL texts

-- ** TeX commands

-- | @texCommand name@ parses @"\\" <name>@.
texCommand :: Text -> Parser st ()
texCommand name = token ("\\" <> name)

-- | @texCommandWithArg name arg@ parses @"\\" <name> "{" <arg> "}"@.
texCommandWithArg :: Text -> Parser st a -> Parser st a
texCommandWithArg name arg = do
  texCommand name
  braced arg

-- | @optInTexArg macroName p@ runs either @p@, or @"\\" <macroname> "{" <p> "}"@.
optInTexArg :: Text -> Parser st a -> Parser st a
optInTexArg macroName p = try p <|> texCommandWithArg macroName p

-- | @texBegin env@ parses @"\\begin" "{" <env> "}"@.
texBegin :: Parser st a -> Parser st a
texBegin = texCommandWithArg "begin"

-- | @texBegin env@ parses @"\\end" "{" <env> "}"@.
texEnd :: Parser st a -> Parser st a
texEnd = texCommandWithArg "end"


-- ** Brackets

-- | @parenthesised p@ parses @"(" <p> ")".
parenthesised :: Parser st a -> Parser st a
parenthesised p = snd <$> enclosed "(" ")" p

-- | @bracketed p@ parses @"[" <p> "]".
bracketed :: Parser st a -> Parser st a
bracketed p = snd <$> enclosed "[" "]" p

-- | @braced p@ parses @"{" <p> "}"@.
braced :: Parser st a -> Parser st a
braced p = snd <$> enclosed "{" "}" p

-- | @braced p@ parses @"{" <p> "}"@.
bracedOrTexBraced :: Parser st a -> Parser st a
bracedOrTexBraced p = do
  token' "{" <|> token' "\\{"
  result <- p
  token' "}" <|> token' "\\}"
  return result

-- | @optParenthesised p@ parses @<p> | "(" <p> ")"@.
optParenthesised :: Parser st a -> Parser st a
optParenthesised p = p -|- parenthesised p

-- | @optBraced p@ parses @<p> | "{" <p> "}"@.
optBraced :: Parser st a -> Parser st a
optBraced p = p -|- braced p


-- ** Dots

-- | Parses @"."@.
dot :: Parser st Position.Range
dot = do
  pos1 <- tokenPos' "." <?> "a dot"
  return $ Position.range (pos1, Position.symbol_explode_string "." pos1)

-- | @finish p@ parses @<p> "."@.
finish :: Parser st a -> Parser st a
finish p = after p dot


-- * Iterating parser usage

-- | @repeatUntil' step end@ repeats a monadic action @step@ until @end@
-- succeeds.
repeatUntil' :: (MonadPlus m, Monoid a) => m a -> m b -> m (a, b)
repeatUntil' step end =
  fmap (mempty,) end
  <|> liftA2 (\next (acc,last) -> (next <> acc, last)) step (repeatUntil' step end)

-- | Like @repeatUntil'@, but aggregates the results with the monoid operation.
repeatUntil :: (MonadPlus m, Monoid a) => m a -> m a -> m a
repeatUntil step = fmap (uncurry (<>)) . repeatUntil' step


-- * Control ambiguity

-- | If @p@ is ambiguous, @narrow p@ fails and reports a well-formedness error.
narrow :: Show a => Parser st a -> Parser st a
narrow p = Parser $ \st ok cerr eerr ->
  let pok err eok cok = case eok ++ cok of
        [_] -> ok err eok cok
        ls  ->  eerr $ newErrorMessage (newWellFormednessMessage ["ambiguity error" <> Text.pack (show (map prResult ls))]) (stPosition st)
  in  runParser p st pok cerr eerr

-- | If @p@ is ambiguous, @narrow p@ fails and reports a well-formedness error.
narrow2 :: Show b => Parser st (a, b) -> Parser st (a, b)
narrow2 p = Parser $ \st ok cerr eerr ->
  let pok err eok cok = case eok ++ cok of
        [_] -> ok err eok cok
        ls  ->  eerr $ newErrorMessage (newWellFormednessMessage ["ambiguity error" <> Text.pack (show (map (snd . prResult) ls))]) (stPosition st)
  in  runParser p st pok cerr eerr

-- | Only take the longest possible parses (by @SourcePos@), discard all others.
takeLongest :: Parser st a -> Parser st a
takeLongest p = Parser $ \st ok cerr eerr ->
  let pok err eok cok
        | null cok  = ok err (longest eok) []
        | otherwise = ok err [] (longest cok)
  in  runParser p st pok cerr eerr
  where
    longest :: [ParseResult st a] -> [ParseResult st a]
    longest = lng []
    lng ls []          = reverse ls
    lng [] (c:cs)      = lng [c] cs
    lng (l:ls) (c:cs) =
      case comparing (stPosition . prState) l c of
        GT -> lng (l:ls) cs
        LT -> lng [c] cs
        EQ -> lng (c:l:ls) cs


-- * Deny parses

-- | @failing p@ fails if @p@ succeeds.
failing :: Parser st a -> Parser st ()
failing p = Parser $ \st ok cerr eerr ->
  let pok _err eok _ =
        if   null eok
        then cerr $ unexpectError (showCurrentToken st) (stPosition st)
        else eerr $ unexpectError (showCurrentToken st) (stPosition st)
      peerr _ = ok (newErrorUnknown (stPosition st)) [PR () st] []
      pcerr _ = ok (newErrorUnknown (stPosition st)) [PR () st] []
  in  runParser p st pok pcerr peerr
  where
    showCurrentToken st = showToken $ head $ stInput st ++ noTokens

-- | Labeling of production rules for better error messages.
infix 0 <?>
(<?>) :: Parser st a -> Text -> Parser st a
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

-- | Labeling of production rules for better error messages.
-- (@label msg p = p <?> msg@)
label :: Text -> Parser st a -> Parser st a
label msg p = p <?> msg


-- * Control error messages

-- | Fail with a well-formedness error.
failWF :: Text -> Parser st a
failWF msg = Parser $ \st _ _ eerr ->
  eerr $ newErrorMessage (newWellFormednessMessage [msg]) (stPosition st)

-- | Do not produce an error message.
noError :: Parser st a -> Parser st a
noError p = Parser $ \st ok cerr eerr ->
  let pok   _err = ok   $ newErrorUnknown (stPosition st)
      pcerr _err = cerr $ newErrorUnknown (stPosition st)
      peerr _err = eerr $ newErrorUnknown (stPosition st)
  in  runParser p st pok pcerr peerr

-- | Parse and keep only results well-formed according to the supplied check;
-- fail if there are none. Here @Just str@ signifies an error.
wellFormedCheck :: (a -> Maybe Text) -> Parser st a -> Parser st a
wellFormedCheck check p = Parser $ \st ok cerr eerr ->
  let pos = stPosition st
      pok err eok cok =
        let wfEok = wf eok; wfCok = wf cok
        in  if   null $ wfEok ++ wfCok
            then notWf err eok cok
            else ok err wfEok wfCok
      notWf _err eok cok =
        eerr $ newErrorMessage (newWellFormednessMessage $ nwf $ eok ++ cok) pos
  in  runParser p st pok cerr eerr
  where
    wf  = filter (isNothing . check . prResult)
    nwf = mapMaybe (check . prResult)

-- | Parse and keep only results well-formed according to the supplied check;
-- fail if there are none with a normal error (and not a well-formedness one).
-- Here @True@ means well-formed.
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
      in  Text.unwords . map showToken . takeWhile ((>=) pos . tokenPos) . filter (not . isEOF) . stInput
        -- TODO: Don't use the default Ord SourcePos instance.


-- * Debugging

-- | In case of failure print the error, in case of success print the result
-- of the function shw.
-- This function is implemented using the impure function @Debug.Trace.trace@
-- and should only be used for debugging purposes.
errorTrace ::
  Text -> (ParseResult st a -> Text) -> Parser st a -> Parser st a
errorTrace lbl shw p = Parser $ \st ok cerr eerr ->
    let nok err eok cok = trace (  "error trace (success) : " ++ Text.unpack lbl ++ "\n"
          ++ tabText ("results (e):\n" ++ tabText (unlines (map (Text.unpack . shw) eok)) )
          ++ tabText ("results (c):\n" ++ tabText (unlines (map (Text.unpack . shw) cok)))
          ++ tabText ("error:\n" ++ tabText (show err))) $ ok err eok cok
        ncerr err = trace ("error trace (consumed): " ++ Text.unpack lbl ++ "\n" ++  tabText (show err)) $ cerr err
        neerr err = trace ("error trace (empty)   : " ++ Text.unpack lbl ++ "\n" ++  tabText (show err)) $ eerr err
    in  runParser p st nok ncerr neerr
    where
      tabText = unlines . map ("   " ++) . lines


-- | Return @()@ if the next token isn't @EOF@.
notEof :: Parser st ()
notEof = Parser $ \st ok _ eerr ->
  case stInput st of
    [] -> eerr $ unexpectError "" Position.none
    (t:_) -> if isEOF t
      then eerr $ unexpectError (showToken t) (tokenPos t)
      else ok (newErrorUnknown (tokenPos t)) [] [PR () st]
