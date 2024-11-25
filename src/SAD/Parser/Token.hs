-- |
-- Module      : SAD.Parser.Token
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Tokenization of input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token (
  -- * Tokens
  Token (tokenPos, tokenText),

  -- * Converting Lexemes to Tokens
  ftlLexemesToTokens,
  texLexemesToTokens,

  -- * Legacy Dependencies
  tokensRange,
  showToken,
  composeTokens,
  isEOF,
  noTokens
) where

import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Lazy qualified as Lazy
import FTLex.Ftl qualified as Ftl
import FTLex.Tex qualified as Tex
import Data.List.NonEmpty qualified as NonEmpty
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Functor ((<&>))
import Data.Maybe qualified as Maybe
import Control.Monad.Trans.State.Strict (evalState, State)
import Control.Monad.State.Class (gets, modify)
import Control.Monad (when)
import Text.Megaparsec hiding (State, Pos, Token)

import SAD.Parser.Lexer
import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


-- * Tokens

-- | A token of a ForTheL text
data Token =
    Token {
      tokenText :: Text
    , tokenPos :: Position.T
    }
  | Comment { tokenPos :: Position.T }
  | EOF { tokenPos :: Position.T }
  deriving (Eq, Ord)


-- * Abstract Error Handling

-- | Report a tokenizing error.
handleError :: (error -> (Text, Position.T)) -> ParseErrorBundle [a] error -> IO b
handleError errorHandler errors = do
  let (errorMsg, errorPos) = showError errors errorHandler
  Message.errorTokenizer errorPos errorMsg

-- | Return an error message and the position of the first error that occured
-- during tokenizing.
showError :: ParseErrorBundle [a] error -> (error -> (Text, Position.T)) -> (Text, Position.T)
showError (ParseErrorBundle parseErrors _) errorHandler = case NonEmpty.head parseErrors of
  TrivialError{} -> unknownError
  FancyError _ errs -> properError errorHandler errs

-- | Located error message for an error that is not handled as a custom error
-- of type "Error" during tokenizing.
unknownError :: (Text, Position.T)
unknownError =
  let msg = "SAD.Parser.Token.unknownError: Unknown tokenizing error. " <>
            "If you see this message, please file an issue."
      pos = Position.none
  in (msg, pos)

-- | Turn a set of tokenizing errors into an error message.
properError :: (error -> (Text, Position.T)) -> Set (ErrorFancy error) -> (Text, Position.T)
properError errorHandler errs =
  case Set.elems errs of
    [] -> unknownError
    err : _ -> fancyError errorHandler err

-- | Turn a tokenizing error into an error message.
fancyError :: (error -> (Text, Position.T)) -> ErrorFancy error -> (Text, Position.T)
fancyError errorHandler err = case err of
  ErrorFail{} -> unknownError
  ErrorIndentation{} -> unknownError
  ErrorCustom err -> errorHandler err


-- * Tokenizing

-- ** FTL

-- *** Running the Tokenizer

-- | Convert a list of FTL lexemes to tokens.
ftlLexemesToTokens :: [FtlLexeme] -> IO [Token]
ftlLexemesToTokens lexemes = filterFtlLexemes lexemes >>= runFtlTokenizer ftlText


type FtlTokenizer resultType = ParsecT () [FtlLexeme] (State ()) resultType

-- | Run an FTL tokenizer.
runFtlTokenizer :: FtlTokenizer resultType
                -- ^ Tokenizer to run
                -> [FtlLexeme]
                -- ^ Input lexemes
                -> IO resultType
runFtlTokenizer tokenizer lexemes =
  case evalState (runParserT tokenizer "" lexemes) () of
    Left err -> handleError (const unknownError) err
    Right tokens -> return tokens


-- *** Primitives

-- | Parse arbitrarily many lexemes after which the end of the input is
-- expected.
ftlText :: FtlTokenizer [Token]
ftlText = do
  tokens <- concat <$> many ftlTokens
  eof
  return $ tokens ++ [EOF Position.none]

-- | Parse a single lexeme.
ftlTokens :: FtlTokenizer [Token]
ftlTokens = choice [
    ftlSymbol,
    ftlWord,
    ftlSpace,
    ftlComment
  ]

-- | Parse a symbol lexeme.
ftlSymbol :: FtlTokenizer [Token]
ftlSymbol = do
  symbol <- satisfy Ftl.isSymbolLexeme
  let text = Text.singleton $ Ftl.symbolContent symbol
      pos = Ftl.sourcePos symbol
  return [Token text pos]

-- | Parse a word lexeme.
ftlWord :: FtlTokenizer [Token]
ftlWord = do
  word <- satisfy Ftl.isWordLexeme
  let text = Ftl.wordContent word
      pos = Ftl.sourcePos word
  return [Token text pos]

-- | Parse a space lexeme.
ftlSpace :: FtlTokenizer [Token]
ftlSpace = do
  satisfy Ftl.isSpaceLexeme
  return []

-- | Parse a comment lexeme.
ftlComment :: FtlTokenizer [Token]
ftlComment = do
  comment <- satisfy Ftl.isCommentLexeme
  let pos = Ftl.sourcePos comment
  return [Comment pos]


-- ** TeX

-- *** Running the Tokenizer

-- | Convert a list of TeX lexemes to tokens.
texLexemesToTokens :: [TexLexeme] -> IO [Token]
texLexemesToTokens lexemes = filterTexLexemes lexemes >>= runTexTokenizer texText texInitState

type TexTokenizer resultType = ParsecT TexError [TexLexeme] (State TexState) resultType

-- | Run a tokenizer.
runTexTokenizer :: TexTokenizer resultType
                -- ^ Tokenizer to run
                -> TexState
                -- ^ Initial lexing state
                -> [TexLexeme]
                -- ^ Input lexemes
                -> IO resultType
runTexTokenizer tokenizer initState lexemes =
  case evalState (runParserT tokenizer "" lexemes) initState of
    Left err -> handleError texMakeErrMsg err
    Right tokens -> return tokens


-- *** Errors

data TexError =
    NestedForthel Position.T
  | InvalidEnvEnd Position.T
  | InvalidGroupEnd Position.T
  | UnclosedGroup Position.T
  | UnclosedEnv Position.T
  | Unexpected Position.T Text Text
  deriving (Eq, Ord)

-- | Turn an error into a located error 
texMakeErrMsg :: TexError -> (Text, Position.T)
texMakeErrMsg (NestedForthel pos) =
  let msg = "Illegal nesting of \"forthel\" groups."
  in (msg, pos)
texMakeErrMsg (InvalidEnvEnd pos) =
  let msg = "Invalid environment ending."
  in (msg, pos)
texMakeErrMsg (InvalidGroupEnd pos) =
  let msg = "Invalid group ending."
  in (msg, pos)
texMakeErrMsg (UnclosedGroup pos) =
  let msg = "Unclosed group."
  in (msg, pos)
texMakeErrMsg (UnclosedEnv pos) =
  let msg = "Unclosed environment."
  in (msg, pos)
texMakeErrMsg (Unexpected pos unexp exp) =
  let msg = "Unexpected " <> unexp <> ". Expected " <> exp <> "."
  in (msg, pos)


-- *** States

data Group =
    TexGroup
  | Environment Text
  deriving (Eq, Ord)


newtype TexState = TexState {
    insideForthel :: Bool
  }

texInitState :: TexState
texInitState = TexState {
    insideForthel = False
}

setInsideForthel :: TexState -> TexState
setInsideForthel state = state{insideForthel = True}

setOutsideForthel :: TexState -> TexState
setOutsideForthel state = state{insideForthel = False}


-- *** Primitives

texText :: TexTokenizer [Token]
texText = do
  tokens <- concat <$> many (texToken <|> catchInvalidGroupEnd <|> catchInvalidEnvEnd)
  eof
  return $ tokens ++ [EOF Position.none]

texToken :: TexTokenizer [Token]
texToken = choice [
    texSpace >>= skip,
    texControlSpace >>= skip,
    texSkipped >>= skip,
    texComment,
    texParameter >>= skipOutsideForthel,
    texMathModeDelimiter >>= skip,
    texBreakCommand >>= skip,
    texGroup (concat <$> many (texToken <|> catchInvalidEnvEnd)),
    texEnvironment (concat <$> many (texToken <|> catchInvalidGroupEnd)),
    texControlWord "section",
    texAnyControlWordExcept ["begin", "end"] >>= skipOutsideForthel,
    texAnyControlSymbol >>= skipOutsideForthel,
    texAnyWord >>= skipOutsideForthel,
    texSymbol >>= skipOutsideForthel
  ]

-- | Parse a space.
texSpace :: TexTokenizer [Token]
texSpace = texAnyCharOfCats [Tex.EndOfLineCat, Tex.SpaceCat]

-- | Parse a control space.
texControlSpace :: TexTokenizer [Token]
texControlSpace = singleTexToken Tex.isControlSpaceLexeme

-- | Parse a skipped lexeme.
texSkipped :: TexTokenizer [Token]
texSkipped = singleTexToken Tex.isSkippedLexeme

-- | Parse a comment.
texComment :: TexTokenizer [Token]
texComment = singleTexToken Tex.isCommentLexeme

-- | Parse a parameter.
texParameter :: TexTokenizer [Token]
texParameter = singleTexToken Tex.isParameterLexeme

-- | Parse a math mode delimiter.
texMathModeDelimiter :: TexTokenizer [Token]
texMathModeDelimiter = choice [
    mkTokens <$> satisfy Tex.isMathShiftCharLexeme,
    texControlSymbol '(',
    texControlSymbol ')',
    texControlSymbol '[',
    texControlSymbol ']'
  ]

-- | Parse a break command.
texBreakCommand :: TexTokenizer [Token]
texBreakCommand = choice [
    texControlSymbol '\\',
    texControlWord "par"
  ]

-- | Parse a symbol.
texSymbol :: TexTokenizer [Token]
texSymbol = texAnyCharOfCats [
    Tex.AlignTabCat,
    Tex.SuperscriptCat,
    Tex.SubscriptCat,
    Tex.OtherCat,
    Tex.ActiveCat
  ]

-- | Parse a TeX group (depending on a parser @p@ for the content of the group).
-- If we are currently inside a ForTheL group, the tokens given by the
-- begin-group lexeme, the result of @p@ and the end-group lexeme are returned;
-- otherwise only the result of @p@ is returned.
texGroup :: TexTokenizer [Token] -> TexTokenizer [Token]
texGroup p = do
  beginGroup <- singleTexToken Tex.isBeginGroupCharLexeme
  let beginGroupPos = tokensPos beginGroup
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedGroup beginGroupPos
  endGroup <- singleTexToken Tex.isEndGroupCharLexeme
  insideForthel <- gets insideForthel
  if insideForthel
    then return $ beginGroup ++ content ++ endGroup
    else return content

-- | Parse an end-group token and throw an error. Useful to catch unbalanced
-- end-group tokens.
catchInvalidGroupEnd :: TexTokenizer a
catchInvalidGroupEnd = do
  endGroup <- singleTexToken Tex.isEndGroupCharLexeme
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
texEnvironment :: TexTokenizer [Token] -> TexTokenizer [Token]
texEnvironment p = do
  currentlyInsideForthel <- gets insideForthel
  -- Parse a @\\begin{...}@ command:
  beginMacro <- texControlWord "begin"
  beginGroup <- catchUnexpected "a begin-group lexeme" $ singleTexToken Tex.isBeginGroupCharLexeme
  envName <- concat <$> some (someTexTokens Tex.isLetterCharLexeme <|> singleTexToken Tex.isOtherCharLexeme)
  endGroup <- catchUnexpected "an end-group lexeme" $ singleTexToken Tex.isEndGroupCharLexeme
  let envNameText = tokensText envName
      beginEnvCommand = beginMacro ++ beginGroup ++ envName ++ endGroup
      beginEnvPos = tokensPos beginEnvCommand
  -- If the environment name is @forthel@ then either fail (if the
  -- @insideForthel@ flag is already set) or set the @insideForthel@ flag:
  when (envNameText == "forthel" && currentlyInsideForthel) $
    customFailure $ NestedForthel (tokensPos beginEnvCommand)
  when (envNameText == "forthel" && not currentlyInsideForthel) $ modify setInsideForthel
  -- Run @p@:
  content <- p
  -- Throw an error if the end of the input is reached:
  ifEofFailWith $ UnclosedEnv beginEnvPos
  -- Parse an @\\end{...}@ command:
  endMacro <- texControlWord "end"
  beginGroup' <- catchUnexpected "a begin-group lexeme" $ singleTexToken Tex.isBeginGroupCharLexeme
  envName' <- concat <$> some (someTexTokens Tex.isLetterCharLexeme <|> singleTexToken Tex.isOtherCharLexeme)
  endGroup' <- catchUnexpected "an end-group lexeme" $ singleTexToken Tex.isEndGroupCharLexeme
  let envNameText' = tokensText envName'
      endEnvCommand = endMacro ++ beginGroup' ++ envName' ++ endGroup'
  -- Check whether the environment of the @\\begin{...}@ and the @\\end{...}@
  -- commands match:
  when (envNameText' /= envNameText) $
    customFailure $ InvalidEnvEnd (tokensPos endEnvCommand)
  -- If the environment name is "@forthel@" then unset the @insideForthel@ flag:
  when (envNameText == "forthel") $ modify setOutsideForthel
  -- If we are (still) inside a ForTheL group then return the tokens of the
  -- @\\begin{...}@ command, the result of @p@ and the tokens of the
  -- @\\end{...}@ command; otherwise return just the result of @p@:
  currentlyInsideForthel' <- gets insideForthel
  if currentlyInsideForthel'
    then return $ beginEnvCommand ++ content ++ endEnvCommand
    else return content

-- | Parse an end-environment token and throw an error. Useful to catch
-- unbalanced end-environment tokens.
catchInvalidEnvEnd :: TexTokenizer a
catchInvalidEnvEnd = do
  endMacro <- texControlWord "end"
  beginGroup <- singleTexToken Tex.isBeginGroupCharLexeme
  envName <- concat <$> some (someTexTokens Tex.isLetterCharLexeme <|> singleTexToken Tex.isOtherCharLexeme)
  endGroup <- singleTexToken Tex.isEndGroupCharLexeme
  let command = endMacro ++ beginGroup ++ envName ++ endGroup
      pos = tokensPos command
  customFailure $ InvalidEnvEnd pos


-- **** Parsing Characters

-- | Parse any character that matches a given character.
texChar :: Char -> TexTokenizer [Token]
texChar char = do
  charLexeme <- satisfy $ \lexeme ->
    Tex.isCharacterLexeme lexeme && Tex.charContent lexeme == char
  let text = Text.singleton $ Tex.charContent charLexeme
      pos = Tex.sourcePos charLexeme
  return [Token text pos]

-- | Parse any character.
texAnyChar :: TexTokenizer [Token]
texAnyChar = do
  charLexeme <- satisfy Tex.isCharacterLexeme
  let text = Text.singleton $ Tex.charContent charLexeme
      pos = Tex.sourcePos charLexeme
  return [Token text pos]

-- | Parse any character that matches any character from a given list.
texCharOf :: [Char] -> TexTokenizer [Token]
texCharOf chars = do
  charLexeme <- satisfy $ \lexeme ->
    Tex.isCharacterLexeme lexeme && Tex.charContent lexeme `elem` chars
  let text = Text.singleton $ Tex.charContent charLexeme
      pos = Tex.sourcePos charLexeme
  return [Token text pos]

-- | Parse any character that does not match any character from a given list.
texCharExcept :: [Char] -> TexTokenizer [Token]
texCharExcept chars = do
  charLexeme <- satisfy $ \lexeme ->
    Tex.isCharacterLexeme lexeme && Tex.charContent lexeme `notElem` chars
  let text = Text.singleton $ Tex.charContent charLexeme
      pos = Tex.sourcePos charLexeme
  return [Token text pos]

-- | Parse any character whose cagetory code matches a given category code.
texAnyCharOfCat :: Tex.CatCode -> TexTokenizer [Token]
texAnyCharOfCat catCode = do
  charLexeme <- satisfy $ \lexeme ->
    Tex.isCharacterLexeme lexeme && Tex.charCatCode lexeme == catCode
  let text = Text.singleton $ Tex.charContent charLexeme
      pos = Tex.sourcePos charLexeme
  return [Token text pos]

-- | Parse any character whose cagetory code matches any category code from a
-- given list.
texAnyCharOfCats :: [Tex.CatCode] -> TexTokenizer [Token]
texAnyCharOfCats catCodes = do
  charLexeme <- satisfy $ \lexeme ->
    Tex.isCharacterLexeme lexeme && Tex.charCatCode lexeme `elem` catCodes
  let text = Text.singleton $ Tex.charContent charLexeme
      pos = Tex.sourcePos charLexeme
  return [Token text pos]

-- | Parse any character whose cagetory code does not match any category code
-- from a given list.
texAnyCharExceptOfCats :: [Tex.CatCode] -> TexTokenizer [Token]
texAnyCharExceptOfCats catCodes = do
  charLexeme <- satisfy $ \lexeme ->
    Tex.isCharacterLexeme lexeme && Tex.charCatCode lexeme `notElem` catCodes
  let text = Text.singleton $ Tex.charContent charLexeme
      pos = Tex.sourcePos charLexeme
  return [Token text pos]


-- **** Parsing Words

-- | Parse any word. Fails if the result does not match a given string.
texWord :: Text -> TexTokenizer [Token]
texWord word = do
  wordLexeme <- concat <$> some (texAnyCharOfCat Tex.LetterCat)
  let text = Text.concat $ map tokenText wordLexeme
      pos = Position.range_position $ tokensRange wordLexeme
  if text == word
    then return [Token text pos]
    else empty

-- | Parse any word.
texAnyWord :: TexTokenizer [Token]
texAnyWord = do
  wordLexeme <- concat <$> some (texAnyCharOfCat Tex.LetterCat)
  let text = Text.concat $ map tokenText wordLexeme
      pos = Position.range_position $ tokensRange wordLexeme
  return [Token text pos]

-- | Parse any word. Fails if the result does not match any string from a given
-- list.
texAnyWordOf :: [Text] -> TexTokenizer [Token]
texAnyWordOf words = do
  wordLexeme <- concat <$> some (texAnyCharOfCat Tex.LetterCat)
  let text = Text.concat $ map tokenText wordLexeme
      pos = Position.range_position $ tokensRange wordLexeme
  if text `elem` words
    then return [Token text pos]
    else empty

-- | Parse any word. Fails if the result matches any string from a given list.
texAnyWordExcept :: [Text] -> TexTokenizer [Token]
texAnyWordExcept words = do
  wordLexeme <- concat <$> some (texAnyCharOfCat Tex.LetterCat)
  let text = Text.concat $ map tokenText wordLexeme
      pos = Position.range_position $ tokensRange wordLexeme
  if text `notElem` words
    then return [Token text pos]
    else empty


-- **** Parsing Control Words

-- | Parse a control word that matches a given string.
texControlWord :: Text -> TexTokenizer [Token]
texControlWord ctrlWord = do
  ctrlWordLexeme <- satisfy $ \lexeme ->
    Tex.isControlWordLexeme lexeme && Tex.ctrlWordContent lexeme == ctrlWord
  let word = Tex.ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = Tex.sourcePos ctrlWordLexeme
  return [Token text pos]

-- | Parse any control word.
texAnyControlWord :: TexTokenizer [Token]
texAnyControlWord = do
  ctrlWordLexeme <- satisfy Tex.isControlWordLexeme
  let word = Tex.ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = Tex.sourcePos ctrlWordLexeme
  return [Token text pos]

-- | Parse a control word that matches any string from a given list.
texAnyControlWordOf :: [Text] -> TexTokenizer [Token]
texAnyControlWordOf ctrlWords = do
  ctrlWordLexeme <- satisfy $ \lexeme ->
    Tex.isControlWordLexeme lexeme && Tex.ctrlWordContent lexeme `elem` ctrlWords
  let word = Tex.ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = Tex.sourcePos ctrlWordLexeme
  return [Token text pos]

-- | Parse a control word that does not match any string from a given list.
texAnyControlWordExcept :: [Text] -> TexTokenizer [Token]
texAnyControlWordExcept ctrlWords = do
  ctrlWordLexeme <- satisfy $ \lexeme ->
    Tex.isControlWordLexeme lexeme && Tex.ctrlWordContent lexeme `notElem` ctrlWords
  let word = Tex.ctrlWordContent ctrlWordLexeme
      text = "\\" <> word
      pos = Tex.sourcePos ctrlWordLexeme
  return [Token text pos]


-- **** Control Symbols

-- | Parse a control symbol that matches a given character.
texControlSymbol :: Char -> TexTokenizer [Token]
texControlSymbol symbol = do
  ctrlSymbolLexeme <- satisfy $ \lexeme ->
    Tex.isControlSymbolLexeme lexeme && Tex.ctrlSymbolContent lexeme == symbol
  let symbol = Text.singleton (Tex.ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = Tex.sourcePos ctrlSymbolLexeme
  return [Token text pos]

-- | Parse any control symbol.
texAnyControlSymbol :: TexTokenizer [Token]
texAnyControlSymbol = do
  ctrlSymbolLexeme <- satisfy Tex.isControlSymbolLexeme
  let symbol = Text.singleton (Tex.ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = Tex.sourcePos ctrlSymbolLexeme
  return [Token text pos]

-- | Parse a control symbol that matches any character from a given list.
texAnyControlSymbolOf :: [Char] -> TexTokenizer [Token]
texAnyControlSymbolOf symbols = do
  ctrlSymbolLexeme <- satisfy $ \lexeme ->
    Tex.isControlSymbolLexeme lexeme && Tex.ctrlSymbolContent lexeme `elem` symbols
  let symbol = Text.singleton (Tex.ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = Tex.sourcePos ctrlSymbolLexeme
  return [Token text pos]

-- | Parse a control symbol that does not match any character from a given list.
texAnyControlSymbolExcept :: [Char] -> TexTokenizer [Token]
texAnyControlSymbolExcept symbols = do
  ctrlSymbolLexeme <- satisfy $ \lexeme ->
    Tex.isControlSymbolLexeme lexeme && Tex.ctrlSymbolContent lexeme `notElem` symbols
  let symbol = Text.singleton (Tex.ctrlSymbolContent ctrlSymbolLexeme)
      text = "\\" <> symbol
      pos = Tex.sourcePos ctrlSymbolLexeme
  return [Token text pos]


-- **** Misc

-- | Ignore the output of a tokenizer @p@. Intended to be used as @p >>= skip@
-- to run @p@ but return the empty list instead of the result of @p@.
skip :: [Token] -> TexTokenizer [Token]
skip _ = return []

-- | Ignore the output of a tokenizer @p@ if we are currently outside a ForTheL
-- block. Intended to be used as @p >>= skipOutsideForthel@ to run @p@ and
-- return either the empty list or the result of @p@ depending on whether we are
-- outside or inside a ForTheL block.
skipOutsideForthel :: [Token] -> TexTokenizer [Token]
skipOutsideForthel tokens = do
  insideForthel <- gets insideForthel
  if insideForthel
    then return tokens
    else return []

-- | If the end of the input is reached, fail with a custom error.
ifEofFailWith :: TexError -> TexTokenizer ()
ifEofFailWith error = do
  isEof <- Maybe.isJust <$> optional eof
  when isEof (customFailure error)

-- | Catch an unexpected lexeme. Trys a parser @p@; if @p@ fails, an error is
-- thrown marking the current lexeme as unexpected and outputs which token was
-- expected instead.
catchUnexpected :: Text -> TexTokenizer a -> TexTokenizer a
catchUnexpected exp p = try p <|> do
  lexeme <- anySingle
  let pos = Tex.sourcePos lexeme
      unexp = case lexeme of
        Tex.Character{} -> "character lexeme"
        Tex.ControlWord{} -> "control word lexeme"
        Tex.ControlSymbol{} -> "control symbol lexeme"
        Tex.ControlSpace{} -> "control space lexeme"
        Tex.Parameter{} -> "parameter lexeme"
        Tex.Skipped{} -> "skipped lexeme"
        Tex.Comment{} -> "comment"
  customFailure $ Unexpected pos unexp exp


-- ** Helpers

-- | Take a list @l@ of lexemes, report all comment lexemes and remove them from
-- @l@.
filterFtlLexemes :: [FtlLexeme] -> IO [FtlLexeme]
filterFtlLexemes [] = return []
filterFtlLexemes (l : ls) = case l of
  Ftl.Comment{Ftl.sourcePos = pos} -> do
    Message.reports [(pos, Markup.comment1)]
    filterFtlLexemes ls
  _ -> fmap (l :) (filterFtlLexemes ls)

-- | Take a list @l@ of lexemes, report all comment lexemes and remove them as
-- well as all skipped lexemes from @l@.
filterTexLexemes :: [TexLexeme] -> IO [TexLexeme]
filterTexLexemes [] = return []
filterTexLexemes (l : ls) = case l of
  Tex.Skipped{} -> filterTexLexemes ls
  Tex.Comment{Tex.sourcePos = pos} -> do
    Message.reports [(pos, Markup.comment1)]
    filterTexLexemes ls
  _ -> fmap (l :) (filterTexLexemes ls)

-- | Turn a lexeme into a (possibly empty) list of tokens.
mkTokens :: TexLexeme -> [Token]
mkTokens Tex.Character{Tex.charContent = c, Tex.charCatCode = cat, Tex.sourcePos = p}
  | cat == Tex.EndOfLineCat = []
  | cat == Tex.SpaceCat = []
  | otherwise = [Token (Text.singleton c) p]
mkTokens Tex.ControlWord{Tex.ctrlWordContent = w, Tex.sourcePos = p} =
  [Token ("\\" <> w) p]
mkTokens Tex.ControlSymbol{Tex.ctrlSymbolContent = s, Tex.sourcePos = p} =
  [Token ("\\" <> Text.singleton s) p]
mkTokens Tex.ControlSpace{} =
  []
mkTokens Tex.Parameter{Tex.paramNumber = n, Tex.sourcePos = p} =
  [Token ("#" <> Text.pack (show n)) p]
mkTokens Tex.Skipped{} =
  []
mkTokens Tex.Comment{Tex.sourcePos = p} =
  [Comment p]

-- | Parse a single lexeme that satisfies a given property.
singleTexToken :: (TexLexeme -> Bool) -> TexTokenizer [Token]
singleTexToken prop = satisfy prop <&> mkTokens

-- | Parse some lexemes that satisfy a given property and merge them into a
-- single token.
someTexTokens :: (TexLexeme -> Bool) -> TexTokenizer [Token]
someTexTokens prop = do
  lexemes <- some (satisfy prop)
  let token = mergeTokens (concatMap mkTokens lexemes)
  return [token]


-- * Legacy Dependencies

-- Get the end position of a token
tokenEndPos :: Token -> Position.T
tokenEndPos tok@Token{} = Position.symbol_explode (tokenText tok) (tokenPos tok)
tokenEndPos tok@Comment{} = tokenPos tok
tokenEndPos tok@EOF{} = tokenPos tok

-- | The range in which the tokens lie
tokensRange :: [Token] -> Position.Range
tokensRange [] = Position.no_range
tokensRange toks = Position.range (tokenPos $ head toks, tokenEndPos $ last toks)

tokensPos :: [Token] -> Position.T
tokensPos = Position.range_position . tokensRange

-- | Concatenate the text components of a list of tokens.
tokensText :: [Token] -> Text
tokensText = Text.concat . map tokenText

-- | Merge a list of tokens into a single token.
mergeTokens :: [Token] -> Token
mergeTokens tokens = Token (tokensText tokens) (tokensPos tokens)

-- | Print a token
showToken :: Token -> Lazy.Text
showToken t@Token{} = Lazy.fromStrict $ tokenText t
showToken t@Comment{} = Lazy.pack "comment"
showToken EOF{} = Lazy.pack "end of input"

-- | Append tokens separated by a single space if they were separated
-- by whitespace before
composeTokens :: [Token] -> Lazy.Text
composeTokens = Lazy.concat . dive
  where
    dive [] = []
    dive [t] = [showToken t]
    dive (t : t' : ts) = if noSpaceBetween t t'
      then showToken t : dive (t' : ts)
      else showToken t : " " : dive (t' : ts)
    noSpaceBetween t t' = case Position.offset_of (tokenPos t) of
        Just n -> case Position.offset_of (tokenPos t') of
          Just m -> n == m + 1
          Nothing -> False
        Nothing -> False

-- | A singleton /end of file/ token, i.e. the result of tokenizing an empty
-- document
noTokens :: [Token]
noTokens = [EOF Position.none]

-- | Determines whether a token is an /end of file/ token
isEOF :: Token -> Bool
isEOF EOF{} = True
isEOF _ = False
