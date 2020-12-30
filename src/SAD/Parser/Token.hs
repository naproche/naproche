{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Tokenization of input.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token
  ( Token (tokenPos, tokenText)
  , TexState (InsideForthelEnv, OutsideForthelEnv, TexDisabled)
  , tokensRange
  , showToken
  , isProperToken
  , tokenize
  , reportComments
  , composeTokens
  , isEOF
  , noTokens
  ) where

import SAD.Core.SourcePos
import qualified Isabelle.Markup as Markup
import qualified SAD.Core.Message as Message

import Data.Char
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text


data Token = Token
  { tokenText :: Text
  , tokenPos :: SourcePos
  , tokenType :: TokenType
  } | EOF { tokenPos :: SourcePos }
  deriving (Eq, Ord)

instance Show Token where
  show Token{tokenText = p, tokenPos = s} = show s ++ show p
  show EOF{} = "EOF"

data TokenType = NoWhiteSpaceBefore | WhiteSpaceBefore | Comment deriving (Eq, Ord, Show)

-- If at some point one uses a more powerful parser for tokenizing, this should be much
-- less messy.
-- | Indicates whether the tokenizer is currently inside a forthel env.
data TexState = InsideForthelEnv | OutsideForthelEnv | TexDisabled

usingTexParser :: TexState -> Bool
usingTexParser InsideForthelEnv = True
usingTexParser OutsideForthelEnv = True
usingTexParser TexDisabled = False

-- | Make a token with @s@ as @tokenText@ and the range from @p@ to the end of @s@.
makeToken :: Text -> SourcePos -> TokenType -> Token
makeToken s pos = Token s (rangePos (SourceRange pos (pos `advanceAlong` s)))

tokenEndPos :: Token -> SourcePos
tokenEndPos tok@Token{} = tokenPos tok `advanceAlong` tokenText tok
tokenEndPos tok@EOF{} = tokenPos tok

-- | The range in which the tokens lie.
tokensRange :: [Token] -> SourceRange
tokensRange [] = noRange
tokensRange toks = makeRange (tokenPos $ head toks, tokenEndPos $ last toks)

-- | Return the @tokenText@ or "end of input" if the token is @EOF@.
showToken :: Token -> Text
showToken t@Token{} = tokenText t
showToken EOF{} = Text.pack "end of input"

isProperToken :: Token -> Bool
isProperToken t@Token{} = case tokenType t of
  NoWhiteSpaceBefore -> True
  WhiteSpaceBefore -> True
  Comment -> False
isProperToken EOF{} = True

noTokens :: [Token]
noTokens = [EOF noSourcePos]

-- | @tokenize commentChars start text@ takes a list of characters @commentChars@ to use
-- for comments when used as first character in the line and a @text@ that gets tokenized
-- starting from the @start@ position.
tokenize :: TexState -> SourcePos -> Text -> [Token]
tokenize texState start = posToken texState start NoWhiteSpaceBefore
  where
    -- Activate the tokenizer when '\begin{forthel}' appears.
    posToken :: TexState -> SourcePos -> TokenType -> Text -> [Token]
    posToken OutsideForthelEnv pos _ s = toks
      where
        (ignoredText, rest) = Text.breakOn "\\begin{forthel}" s
        newPos = advanceAlong pos (ignoredText <> "\\begin{forthel}")
        toks = posToken InsideForthelEnv newPos WhiteSpaceBefore (Text.drop 15 rest)
    
    -- Deactivate the tokenizer when '\end{forthel}' appears.
    posToken InsideForthelEnv pos _ s | start == "\\end{forthel}" = toks
      where
        (start,rest) = Text.splitAt 13 s
        toks = posToken OutsideForthelEnv (advanceAlong pos start) WhiteSpaceBefore rest
        
    -- Make alphanumeric tokens that don't start with whitespace.
    posToken texState pos whitespaceBefore s | not (Text.null lexeme) = tok:toks
      where
        (lexeme, rest) = Text.span isLexeme s
        tok  = makeToken lexeme pos whitespaceBefore
        toks = posToken texState (advanceAlong pos lexeme) NoWhiteSpaceBefore rest
    
    -- Process whitespace.
    posToken texState pos _ s | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace s
        toks = posToken texState (advanceAlong pos white) WhiteSpaceBefore rest
    
    -- Process non-alphanumeric symbol or EOF.
    posToken texState pos whitespaceBefore s = case Text.uncons s of
      Nothing -> [EOF pos]
      Just ('\\', rest) -> tok:toks
        where
          (name, rest') = Text.span isAlpha rest
          cmd = Text.cons '\\' name
          tok = makeToken cmd pos whitespaceBefore
          toks = posToken texState (advanceAlong pos cmd) WhiteSpaceBefore rest'
      Just (c, _) | if usingTexParser texState then c == '%' else c == '#' -> tok:toks
        where
          (comment, rest) = Text.break (== '\n') s
          tok  = makeToken comment pos Comment
          toks = posToken texState (advanceAlong pos comment) whitespaceBefore rest
      Just (c, cs) -> tok:toks
        where
          tok  = makeToken (Text.singleton c) pos whitespaceBefore
          toks = posToken texState (advancePos pos c) NoWhiteSpaceBefore cs


isLexeme :: Char -> Bool
isLexeme c = isAscii c && isAlphaNum c

reportComments :: Token -> Maybe Message.Report
reportComments t@Token{}
  | isProperToken t = Nothing
  | otherwise = Just (tokenPos t, Markup.comment1)
reportComments EOF{} = Nothing

-- | Append tokens separated by a single space if they were separated
-- by whitespace before.
composeTokens :: [Token] -> Text
composeTokens = Text.concat . dive
  where
    dive [] = []
    dive (t:ts) =
      let whitespaceBefore = if tokenType t == WhiteSpaceBefore then Text.singleton ' ' else Text.empty
      in  whitespaceBefore : showToken t : dive ts

isEOF :: Token -> Bool
isEOF EOF{} = True
isEOF _ = False