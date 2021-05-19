{-
Authors: Steffen Frerix (2017 - 2018)

Parser combinators.
-}

{-# LANGUAGE TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Combinators where

import SAD.Core.SourcePos
import SAD.Parser.Base
import SAD.Parser.Token
import SAD.Parser.Error
import SAD.Parser.Primitives

import Control.Applicative
import Control.Monad
import Data.Ord (comparing)
import Data.Maybe (isNothing, catMaybes)
import Debug.Trace
import Data.Text (Text)
import qualified Data.Text as Text
import SAD.Helpers (nubOrd)



-- choices

---- unambiguous choice

------  Choose in LL1 fashion
-- use '<|>' in "Control.Applicative"

-- | Choose with lookahead.
{-# INLINE (</>) #-}
(</>) :: Parser st a -> Parser st a -> Parser st a
(</>) f g = try f <|> g

-- | Try a parser with lookahead.
try :: Parser st a -> Parser st a
try p = Parser $ \st -> case runParser p st of
  Continuation a b c -> Continuation a b c
  ConsumedFail err -> EmptyFail err
  EmptyFail err -> EmptyFail err

-- | Ambiguous choice. Run both parsers and combine the errors and results.
infixr 2 -|-
(-|-) :: forall st a. Parser st a -> Parser st a -> Parser st a
p1 -|- p2 = Parser $ \st -> case runParser p1 st of
  Continuation err eok cok -> case runParser p2 st of
    Continuation err' eok' cok' -> Continuation (err <+> err') (eok ++ eok') (cok ++ cok')
    ConsumedFail err' -> Continuation (err <+> err') eok cok
    EmptyFail err' -> Continuation (err <+> err') eok cok
  ConsumedFail err -> case runParser p2 st of
    Continuation err' a b -> Continuation (err <+>  err') a b
    ConsumedFail err' -> ConsumedFail (err <> err')
    EmptyFail err' -> EmptyFail (err <> err')
  EmptyFail err -> case runParser p2 st of
    Continuation err' a b -> Continuation (err <+>  err') a b
    EmptyFail err' -> EmptyFail (err <> err')
    ConsumedFail err' -> EmptyFail (err <> err')

-- chain parsing combinators

-- | Parse @a@s interleaved by @sep@s keeping all intermediary results.
sepBy :: Parser st a -> Parser st sep -> Parser st [a]
sepBy p sep = do
  a <- p
  as <- opt [] $ sep >> sepBy p sep
  pure $ a:as

-- | Same as @sepBy@ but keep only the largest result.
sepByLL1 :: Parser st a -> Parser st sep -> Parser st [a]
sepByLL1 p sep = do
  a <- p
  as <- optLL1 [] $ sep >> sepByLL1 p sep
  pure $ a:as


opt :: a -> Parser st a -> Parser st a
opt x p = p -|- return x


optLL1 :: a -> Parser st a -> Parser st a
optLL1 x p = p <|> return x


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
-- returning the result of @p@ and two positions indicating the range of the parse.
enclosed :: Text -> Text -> Parser st a -> Parser st ((SourcePos, SourcePos), a)
enclosed begin end p = do
  beginPos <- tokenPos' begin
  result <- p
  endPos <- tokenPos' end
  return ((beginPos, endPos), result)

-- | Mandatory surrounding parentheses, brackets, and braces.
parenthesised, bracketed, braced :: Parser st a -> Parser st a
parenthesised p = snd <$> enclosed "(" ")" p
bracketed p     = snd <$> enclosed "[" "]" p
braced p        = snd <$> enclosed "{" "}" p


-- | Optional parentheses
paren :: Parser st a -> Parser st a
paren p = p -|- parenthesised p

-- | Dot keyword
dot :: Parser st SourceRange
dot = do
  pos1 <- tokenPos' "." <?> "a dot"
  return $ makeRange (pos1, pos1 `advancePos` ".")

-- | mandatory finishing dot
finish :: Parser st a -> Parser st a
finish p = after p dot


-- Iterating parser usage

-- | @repeatUntil step end@ repeats a monadic action @step@ until @end@ succeeds.
repeatUntil' :: (MonadPlus m, Monoid a) => m a -> m b -> m (a, b)
repeatUntil' step end =
  fmap (mempty,) end
  <|> liftA2 (\next (acc,last) -> (next <> acc, last)) step (repeatUntil' step end)

-- | Like @repeatUntil'@, but aggregates the results with the monoid operation.
repeatUntil :: (MonadPlus m, Monoid a) => m a -> m a -> m a
repeatUntil step = fmap (uncurry (<>)) . repeatUntil' step

-- Control ambiguity

-- | If p is ambiguous, fail and report a well-formedness error
narrow :: (Ord a, Show a) => Parser st a -> Parser st a
narrow p = Parser $ \st -> case runParser p st of
  Continuation err eok cok -> case nubOrd $ map prResult $ eok ++ cok of
    [_] -> Continuation err (take 1 eok) (take (1 - length eok) cok)
    ls  -> EmptyFail $ newErrorMessage (newWellFormednessMessage ["ambiguity error" <> Text.pack (show ls)]) (stPosition st)
  f -> f

-- | Only take the longest possible parses (by @SourcePos@), discard all others
takeLongest :: Parser st a -> Parser st a
takeLongest p = Parser $ \st -> case runParser p st of
  Continuation err eok cok
    | null cok  -> Continuation err (longest eok) []
    | otherwise -> Continuation err [] (longest cok)
  f -> f
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



-- Deny parses

-- | Fail if p succeeds
failing :: Parser st a -> Parser st ()
failing p = Parser $ \st -> case runParser p st of
  Continuation _err eok _ ->
    if   null eok
    then ConsumedFail $ unexpectError (showCurrentToken st) (stPosition st)
    else EmptyFail $ unexpectError (showCurrentToken st) (stPosition st)
  EmptyFail _ -> Continuation (newErrorUnknown (stPosition st)) [PR () st] []
  ConsumedFail _ -> Continuation (newErrorUnknown (stPosition st)) [PR () st] []
  where
    showCurrentToken st = showToken $ head $ stInput st ++ noTokens

-- | Labeling of production rules for better error messages
infix 0 <?>
(<?>) :: Parser st a -> Text -> Parser st a
(<?>) p !msg = Parser $ \st -> case runParser p st of
  Continuation err a b -> Continuation (setError (stPosition st) err) a b
  ConsumedFail err -> ConsumedFail err
  EmptyFail err -> EmptyFail $ setError (stPosition st) err
  where
    setError pos err =
      if   pos < errorPos err
      then err
      else setExpectMessage msg err

-- | Labeling of production rules for better error messages
label :: Text -> Parser st a -> Parser st a
label !msg p = p <?> msg



-- Control error messages

-- | Fail with a well-formedness error
failWF :: Text -> Parser st a
failWF msg = Parser $ \st ->
  EmptyFail $ newErrorMessage (newWellFormednessMessage [msg]) (stPosition st)


---- do not produce an error message
noError :: Parser st a -> Parser st a
noError p = Parser $ \st -> case runParser p st of
  Continuation _err a b -> Continuation (newErrorUnknown (stPosition st)) a b
  ConsumedFail _err -> ConsumedFail $ newErrorUnknown (stPosition st)
  EmptyFail _err -> EmptyFail $ newErrorUnknown (stPosition st)


-- | Parse and keep only results well-formed according to the supplied check;
-- fail if there are none. Here @Just str@ signifies an error.
wellFormedCheck :: (a -> Maybe Text) -> Parser st a -> Parser st a
wellFormedCheck check p = Parser $ \st -> case runParser p st of
  Continuation err eok cok ->
    let wfEok = wf eok; wfCok = wf cok
    in  if   null $ wfEok ++ wfCok
        then notWf err eok cok st
        else Continuation err wfEok wfCok
  f -> f
  where
    notWf _err eok cok st =
      EmptyFail $ newErrorMessage (newWellFormednessMessage $ nwf $ eok ++ cok) (stPosition st)
    wf  = filter (isNothing . check . prResult)
    nwf = catMaybes . map (check . prResult)

-- | Parse and keep only results well-formed according to the supplied check;
-- fail if there are none with a normal error (and not a well-formedness one).
-- Here @True@ means well-formed.
lexicalCheck :: (a -> Bool) -> Parser st a -> Parser st a
lexicalCheck check p = Parser $ \st -> case runParser p st of
  Continuation err eok cok ->
    let wfEok = filter (check . prResult) eok
        wfCok = filter (check . prResult) cok
    in  if null $ wfEok ++ wfCok
        then EmptyFail $ unexpectError (unit err st) (stPosition st)
        else Continuation err wfEok wfCok
  f -> f
  where
    unit err =
      let pos = errorPos err
      in  Text.unwords . map showToken . takeWhile ((>=) pos . tokenPos) . filter (not . isEOF) . stInput
        -- TODO: Don't use the default Ord SourcePos instance.


-- Debugging

---- In case of failure print the error, in case of success print the result
---- of the function shw.
---- This function is implemented using the impure function Debug.Trace.trace
---- and should only be used for debugging purposes.
errorTrace ::
  Text -> (ParseResult st a -> Text) -> Parser st a -> Parser st a
errorTrace lbl shw p = Parser $ \st -> case runParser p st of
    Continuation err eok cok -> trace (  "error trace (success) : " ++ Text.unpack lbl ++ "\n"
          ++ tabText ("results (e):\n" ++ tabText (unlines (map (Text.unpack . shw) eok)) )
          ++ tabText ("results (c):\n" ++ tabText (unlines (map (Text.unpack . shw) cok)))
          ++ tabText ("error:\n" ++ tabText (show err))) $ Continuation err eok cok
    ConsumedFail err -> trace ("error trace (consumed): " ++ Text.unpack lbl ++ "\n" ++  tabText (show err)) $ ConsumedFail err
    EmptyFail err -> trace ("error trace (empty)   : " ++ Text.unpack lbl ++ "\n" ++  tabText (show err)) $ EmptyFail err
    where
      tabText = unlines . map ((++) "   ") . lines


-- | Return @()@ if the next token isn't @EOF@.
notEof :: Parser st ()
notEof = Parser $ \st ->
  case stInput st of
    [] -> EmptyFail $ unexpectError "" noSourcePos
    (t:_) -> case isEOF t of
      True  -> EmptyFail $ unexpectError (showToken t) (tokenPos t)
      False -> Continuation (newErrorUnknown (tokenPos t)) [] [PR () st]
