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
import Control.Monad.Trans.State.Strict (evalState, State)
import Control.Monad.State.Class (get, gets, modify)
import Text.Megaparsec hiding (State, Pos, Token, label)

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
    , sourceText :: Text
    }
  | EOF { tokenPos :: Position.T }
  deriving (Eq, Ord)

instance Show Token where
  show :: Token -> String
  show Token{tokenText = p, tokenPos = s} = show p
  show EOF{} = "EOF"


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
  let msg =
        "Unknown tokenizing error. " <>
        "This is likely to be a bug in Naproche. " <>
        "Please file an issue if it has not been reported yet."
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

-- | Convert a list of FTL lexemes to tokens and throw PIDE markup reports for
-- all comments.
ftlLexemesToTokens :: [Ftl.Lexeme PIDE_Pos] -> IO [Token]
ftlLexemesToTokens lexemes = runFtlTokenizer ftlReportsOrTokens lexemes >>= combine

type FtlTokenizer resultType = ParsecT () [Ftl.Lexeme PIDE_Pos] (State ()) resultType

-- | Run an FTL tokenizer.
runFtlTokenizer :: FtlTokenizer resultType
                -- ^ Tokenizer to run
                -> [Ftl.Lexeme PIDE_Pos]
                -- ^ Input lexemes
                -> IO resultType
runFtlTokenizer tokenizer lexemes =
  case evalState (runParserT tokenizer "" lexemes) () of
    Left err -> handleError (const unknownError) err
    Right tokens -> return tokens


-- *** Primitives

-- | Parse arbitrarily many lexemes after which the end of the input is
-- expected.
ftlReportsOrTokens :: FtlTokenizer [Maybe (Either Position.Report Token)]
ftlReportsOrTokens = do
  reportsOrTokens <- many $ choice [
      wrapToken ftlSymbol,
      wrapToken ftlWord,
      skip ftlSpace,
      wrapReport ftlComment
    ]
  eof
  return reportsOrTokens

-- | Parse a symbol lexeme and return a singleton list consisting of a
-- corresponding token.
ftlSymbol :: FtlTokenizer Token
ftlSymbol = do
  symbol <- satisfy Ftl.isSymbolLexeme
  let text = Text.singleton $ Ftl.symbolContent symbol
      pos = fromPIDEPos $ Ftl.sourcePos symbol
  return $ Token text pos text

-- | Parse a word lexeme and return a singleton list consisting of a
-- corresponding token.
ftlWord :: FtlTokenizer Token
ftlWord = do
  word <- satisfy Ftl.isWordLexeme
  let text = Ftl.wordContent word
      pos = fromPIDEPos $ Ftl.sourcePos word
  return $ Token text pos text

-- | Parse a space lexeme and return an empty list of tokens.
ftlSpace :: FtlTokenizer ()
ftlSpace = do
  satisfy Ftl.isSpaceLexeme
  return ()

-- | Parse a comment lexeme and return a corresponding position report.
ftlComment :: FtlTokenizer Position.Report
ftlComment = do
  comment <- satisfy Ftl.isCommentLexeme
  let pos = fromPIDEPos $ Ftl.sourcePos comment
  return (pos, Markup.comment1)


-- ** TeX

-- *** Running the Tokenizer

-- | Convert a list of TeX lexemes to tokens and throw PIDE markup reports for
-- all comments.
texLexemesToTokens :: [Tex.Lexeme PIDE_Pos] -> IO [Token]
texLexemesToTokens lexemes = runTexTokenizer texReportsOrTokens texInitState lexemes >>= combine

type TexTokenizer resultType = ParsecT TexError [Tex.Lexeme PIDE_Pos] (State TexState) resultType

-- | Run a tokenizer.
runTexTokenizer :: TexTokenizer resultType
                -- ^ Tokenizer to run
                -> TexState
                -- ^ Initial lexing state
                -> [Tex.Lexeme PIDE_Pos]
                -- ^ Input lexemes
                -> IO resultType
runTexTokenizer tokenizer initState lexemes =
  case evalState (runParserT tokenizer "" lexemes) initState of
    Left err -> handleError texMakeErrMsg err
    Right tokens -> return tokens


-- *** Errors

data TexError =
    UnclosedForthelEnv Position.T
  | UnopenedForthelEnv Position.T
  | NestedForthelEnvs Position.T
  deriving (Eq, Ord)

-- | Turn an error into a located error 
texMakeErrMsg :: TexError -> (Text, Position.T)
texMakeErrMsg (UnclosedForthelEnv pos) =
  let msg = "Un-closed \"forthel\" environment"
  in (msg, pos)
texMakeErrMsg (UnopenedForthelEnv pos) =
  let msg = "Un-opened \"forthel\" environment"
  in (msg, pos)
texMakeErrMsg (NestedForthelEnvs pos) =
  let msg = "Nested \"forthel\" environments"
  in (msg, pos)


-- *** States

data ForthelState = InsideForthelEnv | OutsideForthelEnv

data TexState = TexState {
    forthelState :: ForthelState,
    -- ^ Indicates whether we are currently inside or outside a @forthel@
    -- environment
    lastBeginForthel :: Position.T
    -- ^ The position of the last un-closed @\\begin{forthel}@ command. If there
    -- (Used for error handling.)
  }

texInitState :: TexState
texInitState = TexState {
    forthelState = OutsideForthelEnv,
    lastBeginForthel = Position.none
}

setForthelState :: ForthelState -> TexState -> TexState
setForthelState x s = s{forthelState = x}

setLastBeginForthel :: Position.T -> TexState -> TexState
setLastBeginForthel pos state = state{lastBeginForthel = pos}


-- *** Primitives

texReportsOrTokens :: TexTokenizer [Maybe (Either Position.Report Token)]
texReportsOrTokens = do
  reportsOrTokens <- many texReportOrToken
  forthelState <- gets forthelState
  case forthelState of
    InsideForthelEnv -> do
      eof
      pos <- gets lastBeginForthel
      customFailure (UnclosedForthelEnv pos)
    OutsideForthelEnv -> eof
  return reportsOrTokens

texReportOrToken :: TexTokenizer (Maybe (Either Position.Report Token))
texReportOrToken = do
  state <- get
  case forthelState state of
    OutsideForthelEnv -> choice [
        wrapReport texComment,
        wrapToken sectionCommand,
        skip texAnyChar,
        skip texAnyControlSymbol,
        skip texControlSpace,
        skip texParameter,
        skip texSkipped,
        skip (beginForthel OutsideForthelEnv),
        skip texAnyControlWord
      ]
    InsideForthelEnv -> choice [
        wrapReport texComment,
        wrapToken texAnyWord,
        wrapToken beginGroupSymbol,
        wrapToken endGroupSymbol,
        wrapToken alignTabSymbol,
        wrapToken superscriptSymbol,
        wrapToken subscriptSymbol,
        wrapToken otherSymbol,
        wrapToken activeSymbol,
        skip mathShiftChar,
        skip spaceChar,
        skip endOfLineChar,
        skip texControlSpace,
        wrapToken texParameter,
        skip texSkipped,
        skip (texControlSymbol '('),
        skip (texControlSymbol ')'),
        skip (texControlSymbol '['),
        skip (texControlSymbol ']'),
        skip (texControlSymbol '\\'),
        wrapToken texAnyControlSymbol,
        skip (texControlWord "left"),
        skip (texControlWord "middle"),
        skip (texControlWord "right"),
        skip (texControlWord "par"),
        skip (beginForthel InsideForthelEnv),
        skip (endForthel InsideForthelEnv),
        wrapToken texAnyControlWord
      ]

-- | Parse @\\begin{forthel}@.
texBeginForthel :: TexTokenizer [Token]
texBeginForthel = do
  texControlWord "begin"
  texBeginGroupChar
  texWord "forthel"
  texEndGroupChar
  return []

-- | Parse @\\begin{forthel}@.
texEndForthel :: TexTokenizer [Token]
texEndForthel = do
  endCommandTok <- texControlWord "end"
  beginGroupTok <- texBeginGroupChar
  forthelWordTok <- texWord "forthel"
  endGroupTok <- texEndGroupChar
  return [endCommandTok, beginGroupTok, forthelWordTok, endGroupTok]

-- | Parse a comment.
texComment :: TexTokenizer Position.Report
texComment = do
  lexeme <- satisfy Tex.isCommentLexeme
  let pos = fromPIDEPos $ Tex.sourcePos lexeme
  return $ (pos, Markup.comment1)

-- | Parse a control word which -- without its escape character -- matches a
-- given string.
texControlWord :: Text -> TexTokenizer Token
texControlWord ctrlWord = do
  lexeme <- satisfy $ \lexeme -> Tex.isControlWordLexeme lexeme && Tex.ctrlWordContent lexeme == ctrlWord
  let text = "\\" <> Tex.ctrlWordContent lexeme
      pos = fromPIDEPos $ Tex.sourcePos lexeme
      sourceText = Tex.sourceText lexeme
  return $ Token text pos sourceText

-- | Parse any control word.
texAnyControlWord :: TexTokenizer Token
texAnyControlWord = do
  lexeme <- satisfy Tex.isControlWordLexeme
  let text = "\\" <> Tex.ctrlWordContent lexeme
      pos = fromPIDEPos $ Tex.sourcePos lexeme
      sourceText = Tex.sourceText lexeme
  return $ Token text pos sourceText

-- | Parse a control symbol that matches a given character.
texControlSymbol :: Char -> TexTokenizer Token
texControlSymbol char = do
  lexeme <- satisfy $ \lexeme -> Tex.isControlSymbolLexeme lexeme && Tex.ctrlSymbolContent lexeme == char
  let text = "\\" <> Text.singleton (Tex.ctrlSymbolContent lexeme)
      pos = fromPIDEPos $ Tex.sourcePos lexeme
      sourceText = Tex.sourceText lexeme
  return $ Token text pos sourceText

-- | Parse any control symbol.
texAnyControlSymbol :: TexTokenizer Token
texAnyControlSymbol = do
  lexeme <- satisfy Tex.isControlSymbolLexeme
  let text = "\\" <> Text.singleton (Tex.ctrlSymbolContent lexeme)
      pos = fromPIDEPos $ Tex.sourcePos lexeme
      sourceText = Tex.sourceText lexeme
  return $ Token text pos sourceText

-- | Parse a control space.
texControlSpace :: TexTokenizer ()
texControlSpace = do
  satisfy Tex.isControlSpaceLexeme
  return ()

-- | Parse a parameter token.
texParameter :: TexTokenizer Token
texParameter = do
  lexeme <- satisfy Tex.isParameterLexeme
  let text = "#" <> (Text.pack . show $ Tex.paramNumber lexeme)
      pos = fromPIDEPos $ Tex.sourcePos lexeme
      sourceText = Tex.sourceText lexeme
  return $ Token text pos sourceText

-- | Parse a piece of input text that has been skippped by the lexer.
texSkipped :: TexTokenizer ()
texSkipped = do
  satisfy Tex.isSkippedLexeme
  return ()

-- | Parse a begin-group character.
texBeginGroupChar :: TexTokenizer Token
texBeginGroupChar = do
  lexeme <- satisfy Tex.isBeginGroupCharLexeme
  let text = Text.singleton $ Tex.charContent lexeme
      pos = fromPIDEPos $ Tex.sourcePos lexeme
      sourceText = Tex.sourceText lexeme
  return $ Token text pos sourceText

-- | Parse an end-group character.
texEndGroupChar :: TexTokenizer Token
texEndGroupChar = do
  lexeme <- satisfy Tex.isEndGroupCharLexeme
  let text = Text.singleton $ Tex.charContent lexeme
      pos = fromPIDEPos $ Tex.sourcePos lexeme
      sourceText = Tex.sourceText lexeme
  return $ Token text pos sourceText

-- | Parse a single character whose character code matches a given one..
texChar :: Char -> TexTokenizer Token
texChar char = do
  lexeme <- satisfy $ \lexeme -> Tex.isCharacterLexeme lexeme && Tex.charContent lexeme == char
  let text = Text.singleton $ Tex.charContent lexeme
      pos = fromPIDEPos $ Tex.sourcePos lexeme
      sourceText = Tex.sourceText lexeme
  return $ Token text pos sourceText

-- | Parse any character.
texAnyChar :: TexTokenizer Token
texAnyChar = do
  lexeme <- satisfy Tex.isCharacterLexeme
  let text = Text.singleton $ Tex.charContent lexeme
      pos = fromPIDEPos $ Tex.sourcePos lexeme
      sourceText = Tex.sourceText lexeme
  return $ Token text pos sourceText

-- | Parse any characters whose cagetory code matches any element of a given
-- set of category codes
texAnyCharOfCats :: Set Tex.CatCode -> TexTokenizer Token
texAnyCharOfCats cat = do
  lexeme <- satisfy $ \lexeme -> Tex.isCharacterLexeme lexeme && Tex.charCatCode lexeme `Set.member` cat
  let text = Text.singleton $ Tex.charContent lexeme
      pos = fromPIDEPos $ Tex.sourcePos lexeme
      sourceText = Tex.sourceText lexeme
  return $ Token text pos sourceText

-- | Parse any characters whose cagetory code matches a given category code.
texAnyCharOfCat :: Tex.CatCode -> TexTokenizer Token
texAnyCharOfCat = texAnyCharOfCats . Set.singleton

-- | Parse a sequence of characters whose character codes match a given
-- non-empty (!) string.
texWord :: String -> TexTokenizer Token
texWord = dive []
  where
    dive tokens "" = error "SAD.Parser.Token.texWord: empty string"
    dive tokens [c] = do
      token <- texChar c
      let tokens' = reverse (token : tokens)
          text = Text.concat $ map tokenText tokens'
          pos = Position.range_position $ tokensRange tokens'
          source = Text.concat $ map sourceText tokens'
      return $ Token text pos source
    dive tokens (c : rest) = do
      token <- texChar c
      dive (token : tokens) rest

-- | Parse any non-empty sequence of letters.
texAnyWord :: TexTokenizer Token
texAnyWord = do
  tokens <- some $ texAnyCharOfCat Tex.LetterCat
  let text = Text.concat $ map tokenText tokens
      pos = Position.range_position $ tokensRange tokens
      source = Text.concat $ map sourceText tokens
  return $ Token text pos source

-- | Parse a math-shift character.
mathShiftChar :: TexTokenizer Token
mathShiftChar = texAnyCharOfCat Tex.MathShiftCat

-- | Parse a space character.
spaceChar :: TexTokenizer Token
spaceChar = texAnyCharOfCat Tex.SpaceCat

-- | Parse an end-of-line character.
endOfLineChar :: TexTokenizer Token
endOfLineChar = texAnyCharOfCat Tex.EndOfLineCat
 
-- | Parse a @section@ command.
sectionCommand :: TexTokenizer Token
sectionCommand = texControlWord "section"

-- | Parse a begin-group symbol.
beginGroupSymbol :: TexTokenizer Token
beginGroupSymbol = texAnyCharOfCat Tex.BeginGroupCat

-- | Parse an end-group symbol.
endGroupSymbol :: TexTokenizer Token
endGroupSymbol = texAnyCharOfCat Tex.EndGroupCat

-- | Parse an alignment-tab symbol.
alignTabSymbol :: TexTokenizer Token
alignTabSymbol = texAnyCharOfCat Tex.AlignTabCat

-- | Parse a superscript symbol.
superscriptSymbol :: TexTokenizer Token
superscriptSymbol = texAnyCharOfCat Tex.SuperscriptCat

-- | Parse a subscript symbol.
subscriptSymbol :: TexTokenizer Token
subscriptSymbol = texAnyCharOfCat Tex.SubscriptCat

-- | Parse an other symbol.
otherSymbol :: TexTokenizer Token
otherSymbol = texAnyCharOfCat Tex.OtherCat

-- | Parse an active symbol.
activeSymbol :: TexTokenizer Token
activeSymbol = texAnyCharOfCat Tex.ActiveCat

-- | Parse a @\\begin{forthel}@ command.
beginForthel :: ForthelState -> TexTokenizer ()
beginForthel forthelState = case forthelState of
  OutsideForthelEnv -> do
    tokens <- try texBeginForthel
    modify (setForthelState InsideForthelEnv)
    let pos = Position.range_position . tokensRange $ tokens
    modify (setLastBeginForthel pos)
    return ()
  InsideForthelEnv -> do
    tokens <- try texBeginForthel
    let pos = Position.range_position . tokensRange $ tokens
    customFailure (NestedForthelEnvs pos)

-- | Parse a @\\end{forthel}@ command.
endForthel :: ForthelState -> TexTokenizer ()
endForthel forthelState = case forthelState of
  InsideForthelEnv -> do
    tokens <- try texEndForthel
    modify (setForthelState OutsideForthelEnv)
    modify (setLastBeginForthel Position.none)
    return ()
  OutsideForthelEnv -> empty


-- ** Helpers

-- Take a list of position reports or tokens, report the reports and return the
-- tokens with an additionally appended @EOF@ token.
combine :: [Maybe (Either Position.Report Token)] -> IO [Token]
combine [] = return [EOF Position.none]
combine (Nothing : rest) = combine rest
combine (Just (Left report) : rest) = Message.reports [report] >> combine rest
combine (Just (Right token) : rest) = fmap (token :) (combine rest)

-- | Turn a tokenizer @p@ into a tokenizer that runs @p@ but returns @Nothing@.
skip :: (Monad m) => m a -> m (Maybe b)
skip p = p >> return Nothing

-- | Turn a tokenizer that returns a token @T@ into a tokenizer that returns
-- @Just (Right T)@.
wrapToken :: (Functor f) => f Token -> f (Maybe (Either Position.Report Token))
wrapToken p = p <&> (Just . Right)

-- | Turn a tokenizer that returns a report @R@ into a tokenizer that returns
-- @Just (Left R)@.
wrapReport :: (Functor f) => f Position.Report -> f (Maybe (Either Position.Report Token))
wrapReport p = p <&> (Just . Left)


-- * Legacy Dependencies

-- Get the end position of a token
tokenEndPos :: Token -> Position.T
tokenEndPos tok@Token{} = Position.symbol_explode (tokenText tok) (tokenPos tok)
tokenEndPos tok@EOF{} = tokenPos tok

-- | The range in which the tokens lie
tokensRange :: [Token] -> Position.Range
tokensRange [] = Position.no_range
tokensRange toks = Position.range (tokenPos $ head toks, tokenEndPos $ last toks)

-- | Print a token
showToken :: Token -> Lazy.Text
showToken t@Token{} = Lazy.fromStrict $ tokenText t
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
