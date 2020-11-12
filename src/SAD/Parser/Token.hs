{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Tokenization of input.
-}

{-# LANGUAGE NamedFieldPuns #-}

module SAD.Parser.Token
  ( Token (tokenPos, tokenText)
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
tokenize :: [Char] -> SourcePos -> Text -> [Token]
tokenize commentChars start = posToken start NoWhiteSpaceBefore
  where
    posToken :: SourcePos -> TokenType -> Text -> [Token]
    -- Make alphanumeric tokens that don't start with whitespace.
    posToken pos whitespaceBefore s | not (Text.null lexem) = tok:toks
      where
        (lexem, rest) = Text.span isLexem s
        tok  = makeToken lexem pos whitespaceBefore
        toks = posToken (advanceAlong pos lexem) NoWhiteSpaceBefore rest
    -- Process whitespace.
    posToken pos _ s | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace s
        toks = posToken (advanceAlong pos white) WhiteSpaceBefore rest
    -- Process non-alphanumeric symbol or EOF.
    posToken pos whitespaceBefore s = case Text.uncons s of
      Nothing -> [EOF pos]
      Just ('\\', rest) -> tok:toks
        where
          (name, rest') = Text.span isAlpha rest
          cmd = Text.cons '\\' name
          tok = makeToken cmd pos whitespaceBefore
          toks = posToken (advanceAlong pos cmd) WhiteSpaceBefore rest'
      Just (c, _) | elem c commentChars -> tok:toks
        where
          (comment, rest) = Text.break (== '\n') s
          tok  = makeToken comment pos Comment
          toks = posToken (advanceAlong pos comment) whitespaceBefore rest
      Just (c, cs) -> tok:toks
        where
          tok  = makeToken (Text.singleton c) pos whitespaceBefore
          toks = posToken (advancePos pos c) NoWhiteSpaceBefore cs


isLexem :: Char -> Bool
isLexem c = isAscii c && isAlphaNum c

reportComments :: Token -> Maybe Message.Report
reportComments t@Token{}
  | isProperToken t = Nothing
  | otherwise = Just (tokenPos t, Markup.comment1)
reportComments EOF{} = Nothing

-- | Append tokens seperated by a single space if they were seperated
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