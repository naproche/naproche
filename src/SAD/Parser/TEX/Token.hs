-- |
-- Module      : SAD.Parser.TEX.Token
-- Copyright   : (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Tokenization of input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.TEX.Token (
  tokenize
) where

import Data.Text (Text)
import Data.Text qualified as Text
import FTLex.Tex hiding (initState)
import Data.Functor ((<&>))
import Data.Maybe qualified as Maybe
import Control.Monad.Trans.State.Strict (evalState, State)
import Control.Monad.State.Class (gets, modify)
import Control.Monad (when)
import Text.Megaparsec hiding (State, Token, token)

import SAD.Parser.Token
import SAD.Parser.TEX.Lexer qualified as TEX
import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


-- * Tokenizing a TEX document

-- | Convert a list of FTL lexemes to tokens.
tokenize :: [TEX.Lexeme] -> IO [Token]
tokenize lexemes = do
  filteredLexems <- filterLexemes lexemes
  case evalState (runParserT document "" filteredLexems) initState of
    Left err -> handleError makeErrMsg err
    Right tokens -> return tokens

-- | Take a list @l@ of lexemes, report all comment lexemes and remove them as
-- well as all skipped lexemes from @l@.
filterLexemes :: [TEX.Lexeme] -> IO [TEX.Lexeme]
filterLexemes [] = return []
filterLexemes (l : ls) = case l of
  Skipped{} -> filterLexemes ls
  Comment{sourcePos = pos} -> do
    Message.reports [(pos, Markup.comment1)]
    filterLexemes ls
  _ -> fmap (l :) (filterLexemes ls)


-- * Tokenizing Errors

data Error =
    NestedForthel Position.T
  | InvalidEnvEnd Position.T
  | InvalidGroupEnd Position.T
  | UnclosedGroup Position.T
  | UnclosedEnv Position.T
  | Unexpected Position.T Text Text
  deriving (Eq, Ord)

-- | Turn an error into a located error 
makeErrMsg :: Error -> (Text, Position.T)
makeErrMsg (NestedForthel pos) =
  let msg = "Illegal nesting of \"forthel\" groups."
  in (msg, pos)
makeErrMsg (InvalidEnvEnd pos) =
  let msg = "Invalid environment ending."
  in (msg, pos)
makeErrMsg (InvalidGroupEnd pos) =
  let msg = "Invalid group ending."
  in (msg, pos)
makeErrMsg (UnclosedGroup pos) =
  let msg = "Unclosed group."
  in (msg, pos)
makeErrMsg (UnclosedEnv pos) =
  let msg = "Unclosed environment."
  in (msg, pos)
makeErrMsg (Unexpected pos unexp exp) =
  let msg = "Unexpected " <> unexp <> ". Expected " <> exp <> "."
  in (msg, pos)


-- * Tokenizing State

newtype TokenizingState = TokenizingState {
    insideForthel :: Bool
  }

initState :: TokenizingState
initState = TokenizingState {
    insideForthel = False
}


-- * Tokenizers

type Tokenizer a = ParsecT Error [TEX.Lexeme] (State TokenizingState) a

-- | Parse a whole TEX document.
document :: Tokenizer [Token]
document = do
  tokens <- concat <$> many (token <|> catchInvalidGroupEnd <|> catchInvalidEnvEnd)
  eof
  return $ tokens ++ [EOF Position.none]

-- | Parse a single token.
token :: Tokenizer [Token]
token = choice [
    space >>= skip,
    controlSpace >>= skip,
    parameter >>= skipOutsideForthel,
    mathModeDelimiter >>= skip,
    ignoredCommand >>= skip,
    textCommand (concat <$> many token),
    inlineForthel (concat <$> many token),
    group (concat <$> many (token <|> catchInvalidEnvEnd)),
    environment (concat <$> many (token <|> catchInvalidGroupEnd)),
    controlWord "section",
    anyControlWordExcept ["begin", "end"] >>= skipOutsideForthel,
    anyControlSymbol >>= skipOutsideForthel,
    anyWord >>= skipOutsideForthel,
    symbol >>= skipOutsideForthel
  ]

-- | Parse a space.
space :: Tokenizer [Token]
space = anyCharOfCats [EndOfLineCat, SpaceCat]

-- | Parse a control space.
controlSpace :: Tokenizer [Token]
controlSpace = singleToken isControlSpaceLexeme

-- | Parse a single parameter lexeme.
parameter :: Tokenizer [Token]
parameter = singleToken isParameterLexeme

-- | Parse a single math mode delimiter.
mathModeDelimiter :: Tokenizer [Token]
mathModeDelimiter = choice [
    anyCharOfCat MathShiftCat,
    controlSymbol '(',
    controlSymbol ')',
    controlSymbol '[',
    controlSymbol ']'
  ]

-- | Parse a single break command.
ignoredCommand :: Tokenizer [Token]
ignoredCommand = choice [
    controlSymbol '\\',
    controlWord "par",
    controlWord "left",
    controlWord "middle",
    controlWord "right"
  ]

-- | Parse a single symbol.
symbol :: Tokenizer [Token]
symbol = anyCharOfCats [
    AlignTabCat,
    ParamCharCat,
    SuperscriptCat,
    SubscriptCat,
    OtherCat,
    ActiveCat
  ]

-- | Parse a TeX group (depending on a parser @p@ for the content of the group).
-- If we are currently inside a ForTheL group, the tokens given by the
-- begin-group lexeme, the result of @p@ and the end-group lexeme are returned;
-- otherwise only the result of @p@ is returned.
group :: Tokenizer [Token] -> Tokenizer [Token]
group p = do
  beginGroup <- singleToken isBeginGroupCharLexeme
  let beginGroupPos = tokensPos beginGroup
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedGroup beginGroupPos
  endGroup <- singleToken isEndGroupCharLexeme
  insideForthel <- gets insideForthel
  if insideForthel
    then return $ beginGroup ++ content ++ endGroup
    else return content

-- | Parse a @\\text{...}@ command, depending on a parser @p@ for the
-- content of the argument of that command, and return the result of @p@.
textCommand :: Tokenizer [Token] -> Tokenizer [Token]
textCommand p = do
  textMacro <- controlWord "text"
  beginGroup <- singleToken isBeginGroupCharLexeme
  let beginGroupPos = tokensPos beginGroup
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedGroup beginGroupPos
  endGroup <- singleToken isEndGroupCharLexeme
  insideForthel <- gets insideForthel
  return content

-- | Parse an @\\inlineforthel{...}@ command, depending on a parser @p@ for the
-- content of the argument of that command, and return the result of @p@, where
-- @p@ is executed with the @insideForthel@ flag set.
inlineForthel :: Tokenizer [Token] -> Tokenizer [Token]
inlineForthel p = do
  currentlyInsideForthel <- gets insideForthel
  inlineforthelMacro <- controlWord "inlineforthel"
  when currentlyInsideForthel $ customFailure $ NestedForthel (tokensPos inlineforthelMacro)
  group $ do
    modify (\state -> state{insideForthel = True})
    content <- p
    modify (\state -> state{insideForthel = False})
    return content

-- | Parse an end-group token and throw an error. Useful to catch unbalanced
-- end-group tokens.
catchInvalidGroupEnd :: Tokenizer a
catchInvalidGroupEnd = do
  endGroup <- singleToken isEndGroupCharLexeme
  let pos = tokensPos endGroup
  customFailure $ InvalidGroupEnd pos

-- | Parse a TeX environment (depending on a parser @p@ for the content of the
-- environment). If we are currently inside a ForTheL group, the tokens given by
-- the @\\begin{...}@ command, the result of @p@ and the @\\end{...}@ command
-- are returned; otherwise only the result of @p@ is returned.
-- 
-- In any of the following situations an error is thrown:
--
-- * A @forthel@ environment is opened when the @insideForthel@ flag is already
--   set.
-- * Theenvironment names in the @\\begin{...}@ and @\\end{...}@ commands do not
--   match.
-- 
-- Moreover, when entering and leaving a @forthel@ environment, the
-- @insideForthel@ flag is set and unset, respectively.
--
-- NOTE: The control word tokenizer must not succeed at @\\begin@ or @\\end@
--       macros!
environment :: Tokenizer [Token] -> Tokenizer [Token]
environment p = do
  currentlyInsideForthel <- gets insideForthel
  -- Parse a @\\begin{...}@ command:
  beginMacro <- controlWord "begin"
  beginGroup <- catchUnexpected "a begin-group lexeme" $ singleToken isBeginGroupCharLexeme
  envName <- concat <$> some (someTokens isLetterCharLexeme <|> singleToken isOtherCharLexeme)
  endGroup <- catchUnexpected "an end-group lexeme" $ singleToken isEndGroupCharLexeme
  let envNameText = tokensText envName
      beginEnvCommand = beginMacro ++ beginGroup ++ envName ++ endGroup
      beginEnvPos = tokensPos beginEnvCommand
  -- If the environment name is @forthel@ then either fail (if the
  -- @insideForthel@ flag is already set) or set the @insideForthel@ flag:
  when (envNameText == "forthel" && currentlyInsideForthel) $
    customFailure $ NestedForthel (tokensPos beginEnvCommand)
  when (envNameText == "forthel" && not currentlyInsideForthel) $ modify (\state -> state{insideForthel = True})
  --
  forthelFlag <- forthelKeyAhead
  let tlsEnvWithForthelFlagOutsideForthelEnv = envNameText `elem` tlsEnvNames && forthelFlag && not currentlyInsideForthel
  when tlsEnvWithForthelFlagOutsideForthelEnv $ modify (\state -> state{insideForthel = True})
  -- Run @p@:
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedEnv beginEnvPos
  -- Parse an @\\end{...}@ command:
  endMacro <- controlWord "end"
  beginGroup' <- catchUnexpected "a begin-group lexeme" $ singleToken isBeginGroupCharLexeme
  envName' <- concat <$> some (someTokens isLetterCharLexeme <|> singleToken isOtherCharLexeme)
  endGroup' <- catchUnexpected "an end-group lexeme" $ singleToken isEndGroupCharLexeme
  let envNameText' = tokensText envName'
      endEnvCommand = endMacro ++ beginGroup' ++ envName' ++ endGroup'
  -- Check whether the environment of the @\\begin{...}@ and the @\\end{...}@
  -- commands match:
  when (envNameText' /= envNameText) $
    customFailure $ InvalidEnvEnd (tokensPos endEnvCommand)
  -- If the environment name is "@forthel@" then unset the @insideForthel@ flag:
  when (envNameText == "forthel") $ modify (\state -> state{insideForthel = False})
  -- If the environment is a TLS environment with set @forthel@ flag outside a
  -- Forthel group, unset the @insideForthel@ flag:
  when tlsEnvWithForthelFlagOutsideForthelEnv $ modify (\state -> state{insideForthel = False})
  -- If we are (still) inside a ForTheL group then return the tokens of the
  -- @\\begin{...}@ command, the result of @p@ and the tokens of the
  -- @\\end{...}@ command; otherwise return just the result of @p@:
  currentlyInsideForthel' <- gets insideForthel
  if currentlyInsideForthel' || tlsEnvWithForthelFlagOutsideForthelEnv
    then return $ beginEnvCommand ++ content ++ endEnvCommand
    else return content
  where
    tlsEnvNames = [
        "signature",
        "signature*",
        "definition",
        "definition*",
        "axiom",
        "axiom*",
        "theorem",
        "theorem*",
        "lemma",
        "lemma*",
        "proposition",
        "proposition*",
        "corollary",
        "corollary*",
        "proof"
      ]

-- | Parse an end-environment token and throw an error. Useful to catch
-- unbalanced end-environment tokens.
catchInvalidEnvEnd :: Tokenizer a
catchInvalidEnvEnd = do
  endMacro <- controlWord "end"
  beginGroup <- singleToken isBeginGroupCharLexeme
  envName <- concat <$> some (someTokens isLetterCharLexeme <|> singleToken isOtherCharLexeme)
  endGroup <- singleToken isEndGroupCharLexeme
  let command = endMacro ++ beginGroup ++ envName ++ endGroup
      pos = tokensPos command
  customFailure $ InvalidEnvEnd pos


-- * Primitives

-- ** Parsing Characters

-- | Parse any character that matches a given character.
char :: Char -> Tokenizer [Token]
char c = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charContent lexeme == c
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | Parse any character.
anyChar :: Tokenizer [Token]
anyChar = do
  charLexeme <- satisfy isCharacterLexeme
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | Parse any character that matches any character from a given list.
charOf :: [Char] -> Tokenizer [Token]
charOf cs = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charContent lexeme `elem` cs
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | Parse any character that does not match any character from a given list.
charExcept :: [Char] -> Tokenizer [Token]
charExcept cs = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charContent lexeme `notElem` cs
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | Parse any character whose cagetory code matches a given category code.
anyCharOfCat :: CatCode -> Tokenizer [Token]
anyCharOfCat catCode = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charCatCode lexeme == catCode
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | Parse any character whose cagetory code matches any category code from a
-- given list.
anyCharOfCats :: [CatCode] -> Tokenizer [Token]
anyCharOfCats catCodes = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charCatCode lexeme `elem` catCodes
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | Parse any character whose cagetory code does not match any category code
-- from a given list.
anyCharExceptOfCats :: [CatCode] -> Tokenizer [Token]
anyCharExceptOfCats catCodes = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charCatCode lexeme `notElem` catCodes
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]


-- ** Parsing Words

-- | Parse any word. Fails if the result does not match a given string.
word :: Text -> Tokenizer [Token]
word w = do
  wordLexeme <- concat <$> some (anyCharOfCat LetterCat)
  let text = Text.concat $ map tokenText wordLexeme
      pos = Position.range_position $ tokensRange wordLexeme
  if text == w
    then return [Token text pos]
    else empty

-- | Parse any word.
anyWord :: Tokenizer [Token]
anyWord = do
  wordLexeme <- concat <$> some (anyCharOfCat LetterCat)
  let text = Text.concat $ map tokenText wordLexeme
      pos = Position.range_position $ tokensRange wordLexeme
  return [Token text pos]

-- | Parse any word. Fails if the result does not match any string from a given
-- list.
anyWordOf :: [Text] -> Tokenizer [Token]
anyWordOf ws = do
  wordLexeme <- concat <$> some (anyCharOfCat LetterCat)
  let text = Text.concat $ map tokenText wordLexeme
      pos = Position.range_position $ tokensRange wordLexeme
  if text `elem` ws
    then return [Token text pos]
    else empty

-- | Parse any word. Fails if the result matches any string from a given list.
anyWordExcept :: [Text] -> Tokenizer [Token]
anyWordExcept ws = do
  wordLexeme <- concat <$> some (anyCharOfCat LetterCat)
  let text = Text.concat $ map tokenText wordLexeme
      pos = Position.range_position $ tokensRange wordLexeme
  if text `notElem` ws
    then return [Token text pos]
    else empty


-- ** Parsing Control Words

-- | Parse a control word that matches a given string.
controlWord :: Text -> Tokenizer [Token]
controlWord cw = do
  ctrlWordLexeme <- satisfy $ \lexeme ->
    isControlWordLexeme lexeme && ctrlWordContent lexeme == cw
  let word = ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = sourcePos ctrlWordLexeme
  return [Token text pos]

-- | Parse any control word.
anyControlWord :: Tokenizer [Token]
anyControlWord = do
  ctrlWordLexeme <- satisfy isControlWordLexeme
  let word = ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = sourcePos ctrlWordLexeme
  return [Token text pos]

-- | Parse a control word that matches any string from a given list.
anyControlWordOf :: [Text] -> Tokenizer [Token]
anyControlWordOf cws = do
  ctrlWordLexeme <- satisfy $ \lexeme ->
    isControlWordLexeme lexeme && ctrlWordContent lexeme `elem` cws
  let word = ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = sourcePos ctrlWordLexeme
  return [Token text pos]

-- | Parse a control word that does not match any string from a given list.
anyControlWordExcept :: [Text] -> Tokenizer [Token]
anyControlWordExcept cws = do
  ctrlWordLexeme <- satisfy $ \lexeme ->
    isControlWordLexeme lexeme && ctrlWordContent lexeme `notElem` cws
  let word = ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = sourcePos ctrlWordLexeme
  return [Token text pos]


-- ** Control Symbols

-- | Parse a control symbol that matches a given character.
controlSymbol :: Char -> Tokenizer [Token]
controlSymbol cs = do
  ctrlSymbolLexeme <- satisfy $ \lexeme ->
    isControlSymbolLexeme lexeme && ctrlSymbolContent lexeme == cs
  let symbol = Text.singleton (ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = sourcePos ctrlSymbolLexeme
  return [Token text pos]

-- | Parse any control symbol.
anyControlSymbol :: Tokenizer [Token]
anyControlSymbol = do
  ctrlSymbolLexeme <- satisfy isControlSymbolLexeme
  let symbol = Text.singleton (ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = sourcePos ctrlSymbolLexeme
  return [Token text pos]

-- | Parse a control symbol that matches any character from a given list.
anyControlSymbolOf :: [Char] -> Tokenizer [Token]
anyControlSymbolOf css = do
  ctrlSymbolLexeme <- satisfy $ \lexeme ->
    isControlSymbolLexeme lexeme && ctrlSymbolContent lexeme `elem` css
  let symbol = Text.singleton (ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = sourcePos ctrlSymbolLexeme
  return [Token text pos]

-- | Parse a control symbol that does not match any character from a given list.
anyControlSymbolExcept :: [Char] -> Tokenizer [Token]
anyControlSymbolExcept css = do
  ctrlSymbolLexeme <- satisfy $ \lexeme ->
    isControlSymbolLexeme lexeme && ctrlSymbolContent lexeme `notElem` css
  let symbol = Text.singleton (ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = sourcePos ctrlSymbolLexeme
  return [Token text pos]


-- ** Misc

forthelKeyAhead :: Tokenizer Bool
forthelKeyAhead = option False $ try $ lookAhead $ do
  openingBracket <- char '['
  word "forthel"
  return True

-- | Ignore the output of a tokenizer @p@. Intended to be used as @p >>= skip@
-- to run @p@ but return the empty list instead of the result of @p@.
skip :: [Token] -> Tokenizer [Token]
skip _ = return []

-- | Ignore the output of a tokenizer @p@ if we are currently outside a ForTheL
-- block. Intended to be used as @p >>= skipOutsideForthel@ to run @p@ and
-- return either the empty list or the result of @p@ depending on whether we are
-- outside or inside a ForTheL block.
skipOutsideForthel :: [Token] -> Tokenizer [Token]
skipOutsideForthel tokens = do
  insideForthel <- gets insideForthel
  if insideForthel
    then return tokens
    else return []

-- | If the end of the input is reached, fail with a custom error.
ifEofFailWith :: Error -> Tokenizer ()
ifEofFailWith error = do
  isEof <- Maybe.isJust <$> optional eof
  when isEof (customFailure error)

-- | Catch an unexpected lexeme. Trys a parser @p@; if @p@ fails, an error is
-- thrown marking the current lexeme as unexpected and outputs which token was
-- expected instead.
catchUnexpected :: Text -> Tokenizer a -> Tokenizer a
catchUnexpected exp p = try p <|> do
  lexeme <- anySingle
  let pos = sourcePos lexeme
      unexp = case lexeme of
        Character{sourceText = s} -> "character \"" <> s <> "\""
        ControlWord{sourceText = s} -> "control word \"" <> s <> "\""
        ControlSymbol{sourceText = s} -> "control symbol \"" <> s <> "\""
        Parameter{sourceText = s} -> "parameter lexeme \"" <> s <> "\""
        _ -> error "SAD.Parser.TEX.Token.catchUnexpected: Unexpected lexeme. " <>
            "If you see this message, please file an issue."
  customFailure $ Unexpected pos unexp exp

-- | Parse a single lexeme that satisfies a given property.
singleToken :: (TEX.Lexeme -> Bool) -> Tokenizer [Token]
singleToken prop = satisfy prop <&> mkTokens

-- | Parse one or more lexemes that satisfy a given property and merge them into
-- a single token.
someTokens :: (TEX.Lexeme -> Bool) -> Tokenizer [Token]
someTokens prop = do
  lexemes <- some (satisfy prop)
  let token = mergeTokens (concatMap mkTokens lexemes)
  return [token]

-- | Turn a lexeme into a (possibly empty) list of tokens.
mkTokens :: TEX.Lexeme -> [Token]
mkTokens Character{charContent = c, charCatCode = cat, sourcePos = p}
  | cat `elem` [EndOfLineCat, SpaceCat] = []
  | otherwise = [Token (Text.singleton c) p]
mkTokens ControlWord{ctrlWordContent = w, sourcePos = p} =
  [Token ("\\" <> w) p]
mkTokens ControlSymbol{ctrlSymbolContent = s, sourcePos = p} =
  [Token ("\\" <> Text.singleton s) p]
mkTokens Parameter{paramNumber = n, sourcePos = p} =
  [Token ("#" <> Text.pack (show n)) p]
mkTokens _ =
  []
