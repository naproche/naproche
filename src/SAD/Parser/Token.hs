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
  , isMathToken
  , isTextToken
  , noTokens
  ) where

import SAD.Core.SourcePos
import qualified Isabelle.Markup as Markup
import qualified SAD.Core.Message as Message

import Data.Char
import Data.Text (Text)
import qualified Data.Text as Text


data Token = Token
  { tokenText :: Text
  , tokenPos :: SourcePos
  , tokenType :: TokenType
  , tokenMode :: TokenMode
  } | EOF { tokenPos :: SourcePos }
  deriving (Eq, Ord)

instance Show Token where
  show Token{tokenText = p, tokenPos = s} = show s ++ show p
  show EOF{} = "EOF"

data TokenType = NoWhiteSpaceBefore | WhiteSpaceBefore | Comment deriving (Eq, Ord, Show)
data TokenMode = TextMode | MathMode deriving (Eq, Show, Ord)

-- | Make a token with @s@ as @tokenText@ and the range from @p@ to the end of @s@.
makeToken :: Text -> SourcePos -> TokenType -> TokenMode -> Token
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

-- | Turn the string into a stream of tokens.
tokenize :: SourcePos -> Text -> [Token]
tokenize start = posToken start NoWhiteSpaceBefore TextMode
  where
    posToken :: SourcePos -> TokenType -> TokenMode -> Text -> [Token]
    posToken pos whitespaceBefore mode s | not (Text.null lexem) = tok:toks
      where
        (lexem, rest) = Text.span isLexem s
        tok  = makeToken lexem pos whitespaceBefore mode
        toks = posToken (advanceAlong pos lexem) NoWhiteSpaceBefore mode rest
    posToken pos _ mode s | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace s
        toks = posToken (advanceAlong pos white) WhiteSpaceBefore mode rest
    posToken pos whitespaceBefore mode s = case Text.uncons s of
      Nothing -> [EOF pos]
      Just ('\\', rest) -> tok:toks
        where
          (name, rest') = Text.span isAlpha rest
          cmd = (Text.cons '\\' name)
          tok = makeToken cmd pos whitespaceBefore mode
          toks = posToken (advanceAlong pos cmd) WhiteSpaceBefore mode rest'
      Just ('$', rest) -> toks
        where
          toks = posToken (advancePos pos '$') NoWhiteSpaceBefore (switchMode mode) rest
          switchMode :: TokenMode -> TokenMode
          switchMode TextMode = MathMode
          switchMode MathMode = TextMode
      Just ('#', _) -> tok:toks
        where
          (comment, rest) = Text.break (== '\n') s
          tok  = makeToken comment pos Comment mode
          toks = posToken (advanceAlong pos comment) whitespaceBefore mode rest
      Just ('%', _) -> tok:toks
        where
          (comment, rest) = Text.break (== '\n') s
          tok  = makeToken comment pos Comment mode
          toks = posToken (advanceAlong pos comment) whitespaceBefore mode rest
      Just (c, cs) -> tok:toks
        where
          tok  = makeToken (Text.singleton c) pos whitespaceBefore mode
          toks = posToken (advancePos pos c) NoWhiteSpaceBefore mode cs


isLexem :: Char -> Bool
isLexem c = (isAscii c && isAlphaNum c) || c == '_'

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

isMathToken, isTextToken :: Token -> Bool
isMathToken Token{tokenMode = MathMode} = True
isMathToken _tok = False
isTextToken Token{tokenMode = TextMode} = True
isTextToken _tok = False