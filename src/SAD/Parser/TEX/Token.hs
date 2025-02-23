-- |
-- Module      : SAD.Parser.TEX.Token
-- Copyright   : (c) 2024 - 2025, Marcel Schütz
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
import Data.List.Extra (concatUnzip)
import Control.Monad.Trans.State.Strict (evalState, State)
import Control.Monad.State.Class (gets, modify)
import Control.Monad (when, unless)
import Text.Megaparsec hiding (State, Token, token)

import SAD.Parser.Token
import SAD.Parser.TEX.Lexer qualified as TEX
import SAD.Core.Message qualified as Message
import SAD.Helpers (failWithMessage)

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


-- * Tokenizing a TEX document

-- | Convert a list of FTL lexemes to tokens.
tokenize :: [TEX.Lexeme] -> IO [Token]
tokenize lexemes = do
  filteredLexems <- filterLexemes lexemes
  case evalState (runParserT document "" filteredLexems) initState of
    Left err -> handleError makeErrMsg err
    Right (tokens, warnings) -> filterTokens tokens warnings

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


-- | Take a list of tokens and a list of warnings, report all warnings and
-- return the tokens.
filterTokens :: [Token] -> [Warning] -> IO [Token]
filterTokens tokens warnings = do
  reportWarnings warnings
  return tokens
  where
  reportWarnings = foldr ((>>) . reportWarning) (return ())
  reportWarning (Warning text pos) = Message.outputTokenizer Message.WARNING pos text


-- * Tokenizing Errors and Warnings

data Error =
    NestedForthel Position.T
  | InvalidEnvEnd Position.T
  | InvalidGroupEnd Position.T
  | UnclosedGroup Position.T
  | UnclosedBracketGroup Position.T
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
makeErrMsg (UnclosedBracketGroup pos) =
  let msg = "Unclosed bracket group."
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
document :: Tokenizer ([Token], [Warning])
document = do
  (tokens, warnings) <- concatUnzip <$> many (token <|> catchInvalidGroupEnd <|> catchInvalidEnvEnd)
  eof
  return (tokens ++ [EOF Position.none], warnings)

-- | Parse a single token.
token :: Tokenizer ([Token], [Warning])
token = choice [
    space >>= skip,
    controlSpace >>= skip,
    parameter >>= skipOutsideForthel,
    mathModeDelimiter >>= skip,
    ignoredCommand >>= skip,
    textCommand (concatUnzip <$> many token) >>= skipOutsideForthel,
    urlCommand >>= skipOutsideForthel,
    pathCommand >>= skipOutsideForthel,
    verbCommand >>= skipOutsideForthel,
    importCommand,
    inputCommand,
    inlineForthel (concatUnzip <$> many token),
    group (concatUnzip <$> many (token <|> catchInvalidEnvEnd)),
    environment (concatUnzip <$> many (token <|> catchInvalidGroupEnd)),
    controlWord' "section",
    anyControlWordExcept ["begin", "end"] >>= skipOutsideForthel',
    anyControlSymbol >>= skipOutsideForthel',
    anyWord >>= skipOutsideForthel',
    symbol >>= skipOutsideForthel
  ]

-- | Parse a space.
space :: Tokenizer ([Token], [Warning])
space = do
  tokens <- anyCharOfCats [EndOfLineCat, SpaceCat]
  return (tokens, [])

-- | Parse a control space.
controlSpace :: Tokenizer ([Token], [Warning])
controlSpace = singleToken isControlSpaceLexeme

-- | Parse a single parameter lexeme.
parameter :: Tokenizer ([Token], [Warning])
parameter = singleToken isParameterLexeme

-- | Parse a single math mode delimiter.
mathModeDelimiter :: Tokenizer ([Token], [Warning])
mathModeDelimiter = do
  tokens <- choice [
      anyCharOfCat MathShiftCat,
      controlSymbol '(',
      controlSymbol ')',
      controlSymbol '[',
      controlSymbol ']'
    ]
  return (tokens, [])

-- | Parse a single break command.
ignoredCommand :: Tokenizer ([Token], [Warning])
ignoredCommand = do
  tokens <- choice [
      controlWord "par",
      controlWord "left",
      controlWord "middle",
      controlWord "right"
    ]
  return (tokens, [])

-- | Parse a single symbol.
symbol :: Tokenizer ([Token], [Warning])
symbol = do
  tokens <- anyCharOfCats [
      AlignTabCat,
      ParamCharCat,
      SuperscriptCat,
      SubscriptCat,
      OtherCat,
      ActiveCat
    ]
  return (tokens, [])

-- | Parse a TeX group (depending on a parser @p@ for the content of the group).
-- If we are currently inside a ForTheL group, the tokens given by the
-- begin-group lexeme, the result of @p@ and the end-group lexeme are returned;
-- otherwise only the result of @p@ is returned.
group :: Tokenizer ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
group p = do
  beginGroup <- singleToken isBeginGroupCharLexeme
  let beginGroupPos = tokensPos (fst beginGroup)
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedGroup beginGroupPos
  endGroup <- singleToken isEndGroupCharLexeme
  insideForthel <- gets insideForthel
  if insideForthel
    then return $ concatTokWarn [beginGroup, content, endGroup]
    else return content

-- | Parse a TeX group (depending on a parser @p@ for the content of the group).
-- and return the tokens given by the begin-group lexeme, the result of @p@ and
-- the end-group lexeme.
group' :: Tokenizer ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
group' p = do
  beginGroup <- singleToken isBeginGroupCharLexeme
  let beginGroupPos = tokensPos (fst beginGroup)
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedGroup beginGroupPos
  endGroup <- singleToken isEndGroupCharLexeme
  insideForthel <- gets insideForthel
  return $ concatTokWarn [beginGroup, content, endGroup]

-- | Parse a TeX group (depending on a parser @p@ for the content of the group).
-- and return the result of @p@.
group'' :: Tokenizer ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
group'' p = do
  beginGroup <- singleToken isBeginGroupCharLexeme
  let beginGroupPos = tokensPos (fst beginGroup)
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedGroup beginGroupPos
  endGroup <- singleToken isEndGroupCharLexeme
  insideForthel <- gets insideForthel
  return content

-- | Parse a bracket group (depending on a parser @p@ for the content of the#
-- group), i.e. a string of the form @"[" <p> "]"@. If we are currently inside a
-- ForTheL group, the tokens given by the opening bracket, the result of @p@ and
-- the closing bracket are returned; otherwise only the result of @p@ is
-- returned.
bracketGroup :: Tokenizer ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
bracketGroup p = do
  beginGroup <- singleToken isBeginBracketGroupCharLexeme
  let beginGroupPos = tokensPos (fst beginGroup)
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedBracketGroup beginGroupPos
  endGroup <- singleToken isEndBracketGroupCharLexeme
  insideForthel <- gets insideForthel
  if insideForthel
    then return $ concatTokWarn [beginGroup, content, endGroup]
    else return content

-- | Parse a bracket group (depending on a parser @p@ for the content of the#
-- group), i.e. a string of the form @"[" <p> "]"@ and return the tokens given
-- by the opening bracket, the result of @p@ and the closing bracket.
bracketGroup' :: Tokenizer ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
bracketGroup' p = do
  beginGroup <- singleToken isBeginBracketGroupCharLexeme
  let beginGroupPos = tokensPos (fst beginGroup)
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedBracketGroup beginGroupPos
  endGroup <- singleToken isEndBracketGroupCharLexeme
  insideForthel <- gets insideForthel
  return $ concatTokWarn [beginGroup, content, endGroup]

-- | Parse a bracket group (depending on a parser @p@ for the content of the#
-- group), i.e. a string of the form @"[" <p> "]"@ and return the result of @p@.
bracketGroup'' :: Tokenizer ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
bracketGroup'' p = do
  beginGroup <- singleToken isBeginBracketGroupCharLexeme
  let beginGroupPos = tokensPos (fst beginGroup)
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedBracketGroup beginGroupPos
  endGroup <- singleToken isEndBracketGroupCharLexeme
  insideForthel <- gets insideForthel
  return content

-- | Parse a @\\text{...}@ command, depending on a parser @p@ for the
-- content of the argument of that command, and return the result of @p@.
textCommand :: Tokenizer ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
textCommand p = do
  controlWord "text"
  group'' p

urlCommand :: Tokenizer ([Token], [Warning])
urlCommand = do
  macro <- controlWord' "url"
  -- Fail if the next lexeme is not a begin-group character lexeme:
  nextLexeme <- lookAhead anySingle
  let nextLexemePos = sourcePos nextLexeme
      nextLexemeKind = showLexemeKind nextLexeme
  unless (isBeginGroupCharLexeme nextLexeme) $ customFailure $ Unexpected nextLexemePos nextLexemeKind "a begin-group character"
  -- Parse the next lexeme again, this time consuming it (where we can be sure
  -- that it is a begin-group character lexeme):
  argument <- group' . fmap concatUnzip . many $ choice [
      controlSpace,
      parameter,
      anyCharExceptOfCats' [EndGroupCat],
      anyControlSymbol',
      anyControlWord'
    ]
  return $ concatTokWarn [macro, argument]

pathCommand :: Tokenizer ([Token], [Warning])
pathCommand = do
  macro <- controlWord' "path"
  -- Fail if the next lexeme is not a begin-group character lexeme:
  nextLexeme <- lookAhead anySingle
  let nextLexemePos = sourcePos nextLexeme
      nextLexemeKind = showLexemeKind nextLexeme
  unless (isBeginGroupCharLexeme nextLexeme) $ customFailure $ Unexpected nextLexemePos nextLexemeKind "a begin-group character"
  -- Parse the next lexeme again, this time consuming it (where we can be sure
  -- that it is a begin-group character lexeme):
  argument <- group' . fmap concatUnzip . many $ choice [
      controlSpace,
      parameter,
      anyCharExceptOfCats' [EndGroupCat],
      anyControlSymbol',
      anyControlWord'
    ]
  return $ concatTokWarn [macro, argument]

verbCommand :: Tokenizer ([Token], [Warning])
verbCommand = do
  macro <- controlWord' "verb"
  mbStar <- optional (char' '*')
  -- Fail if the next lexeme is not a character lexeme:
  nextLexeme <- lookAhead anySingle
  let nextLexemePos = sourcePos nextLexeme
      nextLexemeKind = showLexemeKind nextLexeme
  unless (isCharacterLexeme nextLexeme) $ customFailure $ Unexpected nextLexemePos nextLexemeKind "a character"
  -- Parse the next lexeme again, this time consuming it (where we can be sure
  -- that it is a character lexeme):
  beginDelimiter <- anyChar'
  let delimiterChar = Text.head $ tokensText (fst beginDelimiter)
      beginDelimiterPos = tokensPos (fst beginDelimiter)
  content <- fmap concatUnzip . many $ choice [
      controlSpace,
      parameter,
      anyCharExcept' [delimiterChar],
      anyControlSymbol',
      anyControlWord'
    ]
  -- Fail if the end of the input is reached before the closing delimiter
  -- character:
  ifEofFailWith $ UnclosedGroup beginDelimiterPos
  endDelimiter <- char' delimiterChar
  return $ concatTokWarn [macro, Maybe.fromMaybe ([], []) mbStar, beginDelimiter, content, endDelimiter]

-- | Parse a @\\importmodule[...]{...}@ or @\\usemodule[...]{...}@ command.
importCommand :: Tokenizer ([Token], [Warning])
importCommand = do
  command <- anyControlWordOf' ["importmodule", "usemodule"]
  fstArg <- bracketGroup' $ concatUnzip <$> some (anyWord' <|> anyDigit' <|> char' '/' <|> char' '-' <|> char' '_' <|> char' '.')
  sndArg <- group' $ concatUnzip <$> some (anyWord' <|> anyDigit' <|> char' '/' <|> char' '?' <|> char' '-' <|> char' '_' <|> char' '.')
  return $ concatTokWarn [command, fstArg, sndArg]

-- | Parse a @\\importmodule[...]{...}@ or @\\usemodule[...]{...}@ command.
inputCommand :: Tokenizer ([Token], [Warning])
inputCommand = do
  command <- controlWord' "inputref"
  fstArg <- bracketGroup' $ concatUnzip <$> some (anyWord' <|> anyDigit' <|> char' '/' <|> char' '-' <|> char' '_' <|> char' '.')
  sndArg <- group' $ concatUnzip <$> some (anyWord' <|> anyDigit' <|> char' '/' <|> char' '-' <|> char' '_' <|> char' '.')
  return $ concatTokWarn [command, fstArg, sndArg]

-- | Parse an @\\inlineforthel{...}@ command, depending on a parser @p@ for the
-- content of the argument of that command, and return the result of @p@, where
-- @p@ is executed with the @insideForthel@ flag set.
inlineForthel :: Tokenizer ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
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
  let pos = tokensPos (fst endGroup)
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
-- * The environment names in the @\\begin{...}@ and @\\end{...}@ commands do
--   not match.
-- 
-- Moreover, when entering and leaving a @forthel@ environment, the
-- @insideForthel@ flag is set and unset, respectively.
--
-- NOTE: The control word tokenizer must not succeed at @\\begin@ or @\\end@
--       macros!
environment :: Tokenizer ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
environment p = do
  currentlyInsideForthel <- gets insideForthel
  -- Parse a @\\begin{...}@ command:
  beginMacro <- controlWord' "begin"
  beginGroup <- catchUnexpected "a begin-group lexeme" $ singleToken isBeginGroupCharLexeme
  envName <- concatUnzip <$> some (someTokens isLetterCharLexeme <|> singleToken isOtherCharLexeme)
  endGroup <- catchUnexpected "an end-group lexeme" $ singleToken isEndGroupCharLexeme
  let envNameText = tokensText (fst envName)
      beginEnvCommand = concatTokWarn [beginMacro, beginGroup, envName, endGroup]
      beginEnvPos = tokensPos (fst beginEnvCommand)
  -- Fail if the environment name is @forthel@ and the @insideForthel@ flag is
  -- already set:
  when (envNameText == "forthel" && currentlyInsideForthel) $
    customFailure $ NestedForthel (tokensPos (fst beginEnvCommand))
  -- If the environment name is @verbatim@, consume anything until the next
  -- @\\end{verbatim}@ command regardless of the given parser @p@:
  if envNameText == "verbatim"
    then do
      content <- fmap concatUnzip . many $ choice [
          controlSpace,
          parameter,
          anyChar',
          anyControlSymbol',
          anyControlWordExcept' ["end"],
          try nonVerbatimEndCommand
        ]
      -- Throw an error if the end of the input is reached:
      ifEofFailWith $ UnclosedEnv beginEnvPos
      -- Parse an @\\end{verbatim}@ command:
      endMacro <- controlWord' "end"
      beginGroup' <- singleToken isBeginGroupCharLexeme
      envName' <- word' "verbatim"
      endGroup' <- singleToken isEndGroupCharLexeme
      let beginEnvCommand = concatTokWarn [beginMacro, beginGroup, envName, endGroup]
          endEnvCommand = concatTokWarn [endMacro, beginGroup', envName', endGroup']
      if currentlyInsideForthel
        then return $ concatTokWarn [beginEnvCommand, content, endEnvCommand]
        else return ([], [])
    -- In any other case, parse the content of the environment via the given
    -- parser @p@ (while keeping track of the @forthel@ flag):
    else do
      when (envNameText == "forthel" && not currentlyInsideForthel) $ modify (\state -> state{insideForthel = True})
      -- Check if the @\\begin{...}@ command has an optional argument whose content
      -- begins with the word @forthel@:
      forthelFlag <- forthelKeyAhead
      let tlsEnvWithForthelFlagOutsideForthelEnv = envNameText `elem` tlsEnvNames && forthelFlag && not currentlyInsideForthel
      when tlsEnvWithForthelFlagOutsideForthelEnv $ modify (\state -> state{insideForthel = True})
      -- Run @p@:
      content <- p
      -- Throw an error if the end of the input is reached:
      ifEofFailWith $ UnclosedEnv beginEnvPos
      -- Parse an @\\end{...}@ command:
      endMacro <- controlWord' "end"
      beginGroup' <- catchUnexpected "a begin-group lexeme" $ singleToken isBeginGroupCharLexeme
      envName' <- concatUnzip <$> some (someTokens isLetterCharLexeme <|> singleToken isOtherCharLexeme)
      endGroup' <- catchUnexpected "an end-group lexeme" $ singleToken isEndGroupCharLexeme
      let envNameText' = tokensText (fst envName')
          endEnvCommand = concatTokWarn [endMacro, beginGroup', envName', endGroup']
      -- Check whether the environment of the @\\begin{...}@ and the @\\end{...}@
      -- commands match:
      when (envNameText' /= envNameText) $
        customFailure $ InvalidEnvEnd (tokensPos (fst endEnvCommand))
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
        then return $ concatTokWarn [beginEnvCommand, content, endEnvCommand]
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
        "convention",
        "convention*",
        "proof"
      ]
    -- Parse any @\\end{...}@ command other than @\\end{verbatim}@.
    nonVerbatimEndCommand :: Tokenizer ([Token], [Warning])
    nonVerbatimEndCommand = do
      endMacro <- controlWord' "end"
      beginGroup <- singleToken isBeginGroupCharLexeme
      envName <- concatUnzip <$> some (someTokens isLetterCharLexeme <|> singleToken isOtherCharLexeme)
      endGroup <- singleToken isEndGroupCharLexeme
      let envNameText = tokensText (fst envName)
          endEnvCommand = concatTokWarn [endMacro, beginGroup, envName, endGroup]
      if envNameText == "verbatim"
        then empty
        else return endEnvCommand

-- | Parse an end-environment token and throw an error. Useful to catch
-- unbalanced end-environment tokens.
catchInvalidEnvEnd :: Tokenizer a
catchInvalidEnvEnd = do
  endMacro <- controlWord' "end"
  beginGroup <- singleToken isBeginGroupCharLexeme
  envName <- concatUnzip <$> some (someTokens isLetterCharLexeme <|> singleToken isOtherCharLexeme)
  endGroup <- singleToken isEndGroupCharLexeme
  let command = concatTokWarn [endMacro, beginGroup, envName, endGroup]
      pos = tokensPos (fst command)
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

-- | The same as @char@, but returns an additional empty list of
-- warnings.
char' :: Char -> Tokenizer ([Token], [Warning])
char' c = do
  tokens <- char c
  return (tokens, [])

-- | Parse any character.
anyChar :: Tokenizer [Token]
anyChar = do
  charLexeme <- satisfy isCharacterLexeme
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | The same as @anyChar@, but returns an additional empty list of
-- warnings.
anyChar' :: Tokenizer ([Token], [Warning])
anyChar' = do
  tokens <- anyChar
  return (tokens, [])

-- | Parse any character that matches any character from a given list.
charOf :: [Char] -> Tokenizer [Token]
charOf cs = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charContent lexeme `elem` cs
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | The same as @char@, but returns an additional empty list of
-- warnings.
charOf' :: [Char] -> Tokenizer ([Token], [Warning])
charOf' cs = do
  tokens <- charOf cs
  return (tokens, [])

-- | Parse any character that does not match any character from a given list.
anyCharExcept :: [Char] -> Tokenizer [Token]
anyCharExcept cs = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charContent lexeme `notElem` cs
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | The same as @anyCharExcept@, but returns an additional empty list of
-- warnings.
anyCharExcept' :: [Char] -> Tokenizer ([Token], [Warning])
anyCharExcept' cs = do
  tokens <- anyCharExcept cs
  return (tokens, [])

-- | Parse any character whose cagetory code matches a given category code.
anyCharOfCat :: CatCode -> Tokenizer [Token]
anyCharOfCat catCode = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charCatCode lexeme == catCode
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | The same as @anyCharOfCat@, but returns an additional empty list of
-- warnings.
anyCharOfCat' :: CatCode -> Tokenizer ([Token], [Warning])
anyCharOfCat' catCode = do
  tokens <- anyCharOfCat catCode
  return (tokens, [])

-- | Parse any character whose cagetory code matches any category code from a
-- given list.
anyCharOfCats :: [CatCode] -> Tokenizer [Token]
anyCharOfCats catCodes = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charCatCode lexeme `elem` catCodes
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | The same as @anyCharOfCats@, but returns an additional empty list of
-- warnings.
anyCharOfCats' :: [CatCode] -> Tokenizer ([Token], [Warning])
anyCharOfCats' catCodes = do
  tokens <- anyCharOfCats catCodes
  return (tokens, [])

-- | Parse any character whose cagetory code does not match any category code
-- from a given list.
anyCharExceptOfCats :: [CatCode] -> Tokenizer [Token]
anyCharExceptOfCats catCodes = do
  charLexeme <- satisfy $ \lexeme ->
    isCharacterLexeme lexeme && charCatCode lexeme `notElem` catCodes
  let text = Text.singleton $ charContent charLexeme
      pos = sourcePos charLexeme
  return [Token text pos]

-- | The same as @anyCharExceptOfCats@, but returns an additional empty list of
-- warnings.
anyCharExceptOfCats' :: [CatCode] -> Tokenizer ([Token], [Warning])
anyCharExceptOfCats' catCodes = do
  tokens <- anyCharExceptOfCats catCodes
  return (tokens, [])


-- ** Parsing Numbers

anyDigit :: Tokenizer [Token]
anyDigit = charOf ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

-- | The same as @anyDigit@, but returns an additional empty list of
-- warnings.
anyDigit' :: Tokenizer ([Token], [Warning])
anyDigit' = do
  tokens <- anyDigit
  return (tokens, [])


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

-- | The same as @word@, but returns an additional empty list of
-- warnings.
word' :: Text -> Tokenizer ([Token], [Warning])
word' w = do
  tokens <- word w
  return (tokens, [])

-- | Parse any word.
anyWord :: Tokenizer [Token]
anyWord = do
  wordLexeme <- concat <$> some (anyCharOfCat LetterCat)
  let text = Text.concat $ map tokenText wordLexeme
      pos = Position.range_position $ tokensRange wordLexeme
  return [Token text pos]

-- | The same as @anyWord@, but returns an additional empty list of
-- warnings.
anyWord' :: Tokenizer ([Token], [Warning])
anyWord' = do
  tokens <- anyWord
  return (tokens, [])

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

-- | The same as @anyWordOf@, but returns an additional empty list of
-- warnings.
anyWordOf' :: [Text] -> Tokenizer ([Token], [Warning])
anyWordOf' ws = do
  tokens <- anyWordOf ws
  return (tokens, [])

-- | Parse any word. Fails if the result matches any string from a given list.
anyWordExcept :: [Text] -> Tokenizer [Token]
anyWordExcept ws = do
  wordLexeme <- concat <$> some (anyCharOfCat LetterCat)
  let text = Text.concat $ map tokenText wordLexeme
      pos = Position.range_position $ tokensRange wordLexeme
  if text `notElem` ws
    then return [Token text pos]
    else empty

-- | The same as @anyWordExcept@, but returns an additional empty list of
-- warnings.
anyWordExcept' :: [Text] -> Tokenizer ([Token], [Warning])
anyWordExcept' ws = do
  tokens <- anyWordExcept ws
  return (tokens, [])


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

-- | The same as @controlWord@, but returns an additional empty list of
-- warnings.
controlWord' :: Text -> Tokenizer ([Token], [Warning])
controlWord' cw = do
  tokens <- controlWord cw
  return (tokens, [])

-- | Parse any control word.
anyControlWord :: Tokenizer [Token]
anyControlWord = do
  ctrlWordLexeme <- satisfy isControlWordLexeme
  let word = ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = sourcePos ctrlWordLexeme
  return [Token text pos]

-- | The same as @anyControlWord@, but returns an additional empty list of
-- warnings.
anyControlWord' :: Tokenizer ([Token], [Warning])
anyControlWord' = do
  tokens <- anyControlWord
  return (tokens, [])

-- | Parse a control word that matches any string from a given list.
anyControlWordOf :: [Text] -> Tokenizer [Token]
anyControlWordOf cws = do
  ctrlWordLexeme <- satisfy $ \lexeme ->
    isControlWordLexeme lexeme && ctrlWordContent lexeme `elem` cws
  let word = ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = sourcePos ctrlWordLexeme
  return [Token text pos]

-- | The same as @anyControlWordOf@, but returns an additional empty list of
-- warnings.
anyControlWordOf' :: [Text] -> Tokenizer ([Token], [Warning])
anyControlWordOf' cws = do
  tokens <- anyControlWordOf cws
  return (tokens, [])

-- | Parse a control word that does not match any string from a given list.
anyControlWordExcept :: [Text] -> Tokenizer [Token]
anyControlWordExcept cws = do
  ctrlWordLexeme <- satisfy $ \lexeme ->
    isControlWordLexeme lexeme && ctrlWordContent lexeme `notElem` cws
  let word = ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = sourcePos ctrlWordLexeme
  return [Token text pos]

-- | The same as @anyControlWordExcept@, but returns an additional empty list of
-- warnings.
anyControlWordExcept' :: [Text] -> Tokenizer ([Token], [Warning])
anyControlWordExcept' cws = do
  tokens <- anyControlWordExcept cws
  return (tokens, [])


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

-- | The same as @controlSymbol@, but returns an additional empty list of
-- warnings.
controlSymbol' :: Char -> Tokenizer ([Token], [Warning])
controlSymbol' cs = do
  tokens <- controlSymbol cs
  return (tokens, [])

-- | Parse any control symbol.
anyControlSymbol :: Tokenizer [Token]
anyControlSymbol = do
  ctrlSymbolLexeme <- satisfy isControlSymbolLexeme
  let symbol = Text.singleton (ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = sourcePos ctrlSymbolLexeme
  return [Token text pos]

-- | The same as @anyControlSymbol@, but returns an additional empty list of
-- warnings.
anyControlSymbol' :: Tokenizer ([Token], [Warning])
anyControlSymbol' = do
  tokens <- anyControlSymbol
  return (tokens, [])

-- | Parse a control symbol that matches any character from a given list.
anyControlSymbolOf :: [Char] -> Tokenizer [Token]
anyControlSymbolOf css = do
  ctrlSymbolLexeme <- satisfy $ \lexeme ->
    isControlSymbolLexeme lexeme && ctrlSymbolContent lexeme `elem` css
  let symbol = Text.singleton (ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = sourcePos ctrlSymbolLexeme
  return [Token text pos]

-- | The same as @anyControlSymbolOf@, but returns an additional empty list of
-- warnings.
anyControlSymbolOf' :: [Char] -> Tokenizer ([Token], [Warning])
anyControlSymbolOf' css  = do
  tokens <- anyControlSymbolOf css
  return (tokens, [])

-- | Parse a control symbol that does not match any character from a given list.
anyControlSymbolExcept :: [Char] -> Tokenizer [Token]
anyControlSymbolExcept css = do
  ctrlSymbolLexeme <- satisfy $ \lexeme ->
    isControlSymbolLexeme lexeme && ctrlSymbolContent lexeme `notElem` css
  let symbol = Text.singleton (ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = sourcePos ctrlSymbolLexeme
  return [Token text pos]

-- | The same as @anyControlSymbolExcept@, but returns an additional empty list of
-- warnings.
anyControlSymbolExcept' :: [Char] -> Tokenizer ([Token], [Warning])
anyControlSymbolExcept' css  = do
  tokens <- anyControlSymbolExcept css
  return (tokens, [])


-- ** Misc

isBeginBracketGroupCharLexeme :: TEX.Lexeme -> Bool
isBeginBracketGroupCharLexeme lexeme = isCharacterLexeme lexeme && charContent lexeme == '['

isEndBracketGroupCharLexeme :: TEX.Lexeme -> Bool
isEndBracketGroupCharLexeme lexeme = isCharacterLexeme lexeme && charContent lexeme == ']'

forthelKeyAhead :: Tokenizer Bool
forthelKeyAhead = option False $ try $ lookAhead $ do
  openingBracket <- char '['
  word "forthel"
  return True

-- | Ignore the output of a tokenizer @p@. Intended to be used as @p >>= skip@
-- to run @p@ but return the empty list instead of the result of @p@.
skip :: ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
skip (_, warnings) = return ([], warnings)

-- | Ignore the output of a tokenizer @p@ if we are currently outside a ForTheL
-- block. Intended to be used as @p >>= skipOutsideForthel@ to run @p@ and
-- return either the empty list or the result of @p@ depending on whether we are
-- outside or inside a ForTheL block.
skipOutsideForthel :: ([Token], [Warning]) -> Tokenizer ([Token], [Warning])
skipOutsideForthel (tokens, warnings) = do
  insideForthel <- gets insideForthel
  if insideForthel
    then return (tokens, warnings)
    else return ([], warnings)

-- | The same as @skipOutsideForthel@, but does not take a list of warnings as
-- argument.
skipOutsideForthel' :: [Token] -> Tokenizer ([Token], [Warning])
skipOutsideForthel' tokens = do
  insideForthel <- gets insideForthel
  if insideForthel
    then return (tokens, [])
    else return ([], [])

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
        _ -> failWithMessage "SAD.Parser.TEX.Token.catchUnexpected" "Unexpected lexeme."
  customFailure $ Unexpected pos unexp exp

-- | Parse a single lexeme that satisfies a given property.
singleToken :: (TEX.Lexeme -> Bool) -> Tokenizer ([Token], [Warning])
singleToken prop = do
  tokens <- satisfy prop <&> mkTokens
  return (tokens, [])

-- | Parse one or more lexemes that satisfy a given property and merge them into
-- a single token.
someTokens :: (TEX.Lexeme -> Bool) -> Tokenizer ([Token], [Warning])
someTokens prop = do
  lexemes <- some (satisfy prop)
  let token = mergeTokens (concatMap mkTokens lexemes)
  return ([token], [])

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

showLexemeKind :: Lexeme Position.T -> Text
showLexemeKind lexeme = case lexeme of
  Character{} -> "character lexeme"
  ControlWord{} -> "control word lexeme"
  ControlSymbol{} -> "control symbol lexeme"
  ControlSpace{} -> "control space lexeme"
  Parameter{} -> "parameter lexeme"
  Skipped{} -> "skipped lexeme"
  Comment{} -> "comment lexeme"
