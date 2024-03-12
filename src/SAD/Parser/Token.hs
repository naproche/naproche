-- |
-- Author: Andrei Paskevich (2001 - 2008),
--         Steffen Frerix (2017 - 2018)
--
-- Tokenization of input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token (
  -- * Tokens
  Token (tokenType, tokenPos, tokenText),
  TokenType (..),
  tokensRange,
  showToken,
  isProperToken,

  -- * Tokenizing ForTheL texts
  tokenize,

  -- * Helper functions
  reportComments,
  composeTokens,
  isEOF,
  noTokens
) where

import Data.Char
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text

import SAD.Data.Instr (ParserKind(..))

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


-- | A token of a ForTheL text
data Token =
    Token {
      tokenText :: Text
    , tokenPos :: Position.T
    , tokenType :: TokenType
    }
  | EOF { tokenPos :: Position.T }
  deriving (Eq, Ord)

instance Show Token where
  show Token{tokenText = p, tokenPos = s} = show p
  show EOF{} = "EOF"

data TokenType =
    NoWhiteSpaceBefore  -- a regular token without preceding whitespace
  | WhiteSpaceBefore    -- a regular token with preceding whitespace
  | Comment             -- a comment
  deriving (Eq, Ord, Show)

-- Indicates whether the tokenizer is currently inside a forthel environment
data TexState = InsideForthelEnv | OutsideForthelEnv deriving (Eq)

-- Generate a token with a given range
makeTokenRange :: Text -> Position.Range -> TokenType -> Token
makeTokenRange text range = Token text (Position.range_position range)

-- Generate a new token with a given starting position
makeToken :: Text -> Position.T -> TokenType -> Token
makeToken text pos = makeTokenRange text (pos, Position.symbol_explode text pos)

-- Get the end position of a token
tokenEndPos :: Token -> Position.T
tokenEndPos tok@Token{} = Position.symbol_explode (tokenText tok) (tokenPos tok)
tokenEndPos tok@EOF{} = tokenPos tok

-- | The range in which the tokens lie
tokensRange :: [Token] -> Position.Range
tokensRange [] = Position.no_range
tokensRange toks = Position.range (tokenPos $ head toks, tokenEndPos $ last toks)

-- | Print a token
showToken :: Token -> Text
showToken t@Token{} = tokenText t
showToken EOF{} = Text.pack "end of input"

-- | Determine whether a given token is /proper/, i.e. not a comment
isProperToken :: Token -> Bool
isProperToken t@Token{} = case tokenType t of
  NoWhiteSpaceBefore -> True
  WhiteSpaceBefore -> True
  Comment -> False
isProperToken EOF{} = True

isLexeme :: Char -> Bool
isLexeme c = isAscii c && isAlphaNum c


-- | Tokenize a ForTheL text (depending on a ForTheL dialect and a starting
-- position)
--
-- If @Dialect@ is chosen to be @FTL@ then the text is tokenized as follows:
--
--  * Any alphanumeric string becomes a token
--  * Any symbolic character becomes a token
--  * Everything from a @#@ to the next linebreak becomes a comment token
--  * Whitespaces are ignored
--
-- If @Dialect@ is chosen to be @TEX@ then the text is tokenized as follows
--
--  * Everything not enclosed within "@\\begin{forthel}@" and "@\\end{forthel}@"
--    is ignored
--  * Any alphanumeric string becomes a token
--  * Any symbolic character becomes a token
--  * LaTeX commands for logical symbols and certain special commands are first
--    converted to ASCII representations (e.g. @\\wedge@ to @/\\@) and then
--    tokenized by the above rules
--  * Any expression of the form @\\{@ or @\\}@ is transformed to @{@ or @}@,
--    resp. which then becomes a single token
--  * LaTeX commands for greek letters are also converted to alphanumeric
--    strings and then also tokenized by the above rules
--  * Everything from a @%@ to the next linebreak becomes a comment token
--  * Any whitespace and any expression of the form @\\\\@, @\\[@, @\\]@, @\\(@,
--    @\\)@, @$@, @\\left@, @\\middle@, @\\right@ is ignored
tokenize :: ParserKind -> Position.T -> Text -> [Token]

-- Tokenize an FTL document
tokenize Ftl startPos = procToken startPos NoWhiteSpaceBefore
  where
    -- Process a token
    procToken :: Position.T -> TokenType -> Text -> [Token]
    -- Process alphanumeric token
    procToken currentPos whitespaceBefore remainingText
      | not (Text.null lexeme) = tok:toks
      where
        (lexeme, rest) = Text.span isLexeme remainingText
        tok  = makeToken lexeme currentPos whitespaceBefore
        toks = procToken (Position.symbol_explode lexeme currentPos) NoWhiteSpaceBefore rest
    -- Process whitespace
    procToken currentPos _ remainingText
      | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace remainingText
        toks = procToken (Position.symbol_explode white currentPos) WhiteSpaceBefore rest
    -- Process EOF, comment or symbolic token
    procToken currentPos whitespaceBefore remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> [EOF currentPos]
        -- Comment
        Just ('#', _) -> tok:toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            tok  = makeToken comment currentPos Comment
            toks = procToken (Position.symbol_explode comment currentPos) whitespaceBefore rest
        -- Symbolic token
        Just (c, cs) -> tok:toks
          where
            text = Text.singleton c
            tok  = makeToken text currentPos whitespaceBefore
            toks = procToken (Position.symbol_explode text currentPos) NoWhiteSpaceBefore cs

-- Tokenize an FTL-TeX document
tokenize Tex startPos = procToken OutsideForthelEnv startPos NoWhiteSpaceBefore
  where
    -- Process a token
    procToken :: TexState -> Position.T -> TokenType -> Text -> [Token]
    -- When outside a forthel environment, ignore anything till the next
    -- occurence of "\begin{forthel}" and then switch to 'InsideForthelEnv' mode
    -- TODO: Handle commented "\begin{forthel}" expressions
    procToken OutsideForthelEnv currentPos _ remainingText = toks
      where
        (ignoredText, rest) = Text.breakOn "\\begin{forthel}" remainingText
        newPos = Position.symbol_explode (ignoredText <> "\\begin{forthel}") currentPos
        toks = procToken InsideForthelEnv newPos WhiteSpaceBefore $ Text.drop (Text.length "\\begin{forthel}") rest
    -- When we reach an "\end{forthel}" expression inside a forthen environment,
    -- switch to 'OutsideForthelEnv' mode
    procToken InsideForthelEnv currentPos _ remainingText
      | start == "\\end{forthel}" = toks
      where
        (start, rest) = Text.splitAt (Text.length "\\end{forthel}") remainingText
        toks = procToken OutsideForthelEnv (Position.symbol_explode start currentPos) WhiteSpaceBefore rest
    -- Process alphanumeric token
    procToken InsideForthelEnv currentPos whitespaceBefore remainingText
      | not (Text.null lexeme) = tok:toks
      where
        (lexeme, rest) = Text.span isLexeme remainingText
        tok  = makeToken lexeme currentPos whitespaceBefore
        toks = procToken InsideForthelEnv (Position.symbol_explode lexeme currentPos) NoWhiteSpaceBefore rest
    -- Process whitespace
    procToken InsideForthelEnv currentPos _ remainingText
      | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace remainingText
        toks = procToken InsideForthelEnv (Position.symbol_explode white currentPos) WhiteSpaceBefore rest
    -- Process line break
    procToken InsideForthelEnv currentPos _ remainingText
      | head == "\\\\" = toks
      where
        (head, rest) = Text.splitAt (Text.length "\\\\") remainingText
        toks = procToken InsideForthelEnv (Position.symbol_explode head currentPos) WhiteSpaceBefore rest
    -- Display style math mode delimiters
    procToken InsideForthelEnv currentPos _ remainingText
      | head `elem` ["\\[", "\\]", "\\(", "\\)"] = toks
      where
        (head, rest) = Text.splitAt 2 remainingText
        toks = procToken InsideForthelEnv (Position.symbol_explode head currentPos) WhiteSpaceBefore rest
    -- Process non-alphanumeric symbol or EOF
    procToken InsideForthelEnv currentPos whitespaceBefore remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> [EOF currentPos]
        -- Inline math mode delimiter
        Just ('$', rest) -> procToken InsideForthelEnv (Position.symbol_explode_string "$" currentPos) WhiteSpaceBefore rest
        -- Comment
        Just ('%', _) -> tok:toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            tok  = makeToken comment currentPos Comment
            toks = procToken InsideForthelEnv (Position.symbol_explode comment currentPos) WhiteSpaceBefore rest
        -- Escaped special character
        Just ('\\', rest)
          | Text.head rest `elem` ['{', '}'] ->
            procToken InsideForthelEnv (Position.symbol_explode_string "\\" currentPos) NoWhiteSpaceBefore rest
        -- TeX command
        Just ('\\', rest) -> case name of
          "left" -> toks
          "middle" -> toks
          "right" -> toks
          _ -> tok : toks
          where
            (name, rest') = Text.span isAlpha rest
            newPos = Position.symbol_explode (Text.cons '\\' name) currentPos
            tok = makeTokenRange (Text.cons '\\' name) (currentPos, newPos) whitespaceBefore
            toks = procToken InsideForthelEnv newPos NoWhiteSpaceBefore rest'
        -- Symbolic token
        Just (c, cs) -> tok:toks
          where
            text = Text.singleton c
            tok  = makeToken text currentPos whitespaceBefore
            toks = procToken InsideForthelEnv (Position.symbol_explode text currentPos) NoWhiteSpaceBefore cs


-- | Markup report for comments
reportComments :: Token -> Maybe Position.Report
reportComments t@Token{}
  | isProperToken t = Nothing
  | otherwise = Just (tokenPos t, Markup.comment1)
reportComments EOF{} = Nothing

-- | Append tokens separated by a single space if they were separated
-- by whitespace before
composeTokens :: [Token] -> Text
composeTokens = Text.concat . dive
  where
    dive [] = []
    dive (t:ts) =
      let whitespaceBefore = if tokenType t == WhiteSpaceBefore then Text.singleton ' ' else Text.empty
      in  whitespaceBefore : showToken t : dive ts

-- | A singleton /end of file/ token, i.e. the result of tokenizing an empty
-- document
noTokens :: [Token]
noTokens = [EOF Position.none]

-- | Determines whether a token is an /end of file/ token
isEOF :: Token -> Bool
isEOF EOF{} = True
isEOF _ = False
