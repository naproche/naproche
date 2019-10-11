{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Tokenization of input.
-}

{-# LANGUAGE NamedFieldPuns #-}

module SAD.Parser.Token
  ( Token (tokenPos, tokenProofText),
    tokensRange,
    showToken,
    properToken,
    tokenize,
    reportComments,
    composeTokens,
    isEOF,
    noTokens)
  where

import Data.Char

import SAD.Core.SourcePos
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import qualified SAD.Core.Message as Message
import qualified Isabelle.Markup as Markup


data Token = Token
  { tokenProofText :: Text
  , tokenPos :: SourcePos
  , tokenType :: TokenType
  } | EOF { tokenPos :: SourcePos }
  deriving (Eq, Ord)

instance Show Token where
  show (Token p s _) = show s ++ show p
  show (EOF _) = "EOF"

data TokenType = NoWhiteSpaceBefore | WhiteSpaceBefore | Comment deriving (Eq, Ord, Show)

-- | Make a token with @s@ as @tokenProofText@ and the range from @p@ to the end of @s@.
makeToken :: Text -> SourcePos -> TokenType -> Token
makeToken s pos = Token s (rangePos (SourceRange pos (pos `advanceAlong` s)))

tokenEndPos :: Token -> SourcePos
tokenEndPos tok@Token{} = tokenPos tok `advanceAlong` tokenProofText tok
tokenEndPos tok@EOF {} = tokenPos tok

-- | The range in which the tokens lie.
tokensRange :: [Token] -> SourceRange
tokensRange [] = noRange
tokensRange toks = makeRange (tokenPos $ head toks, tokenEndPos $ last toks)

-- | Return the @tokenProofText@ or "end of input" if the token is @EOF@.
showToken :: Token -> Text
showToken t@Token{} = tokenProofText t
showToken EOF{} = Text.pack "end of input"

properToken :: Token -> Bool
properToken t@(Token _ _ _) = case tokenType t of
  NoWhiteSpaceBefore -> True
  WhiteSpaceBefore -> True
  Comment -> False
properToken EOF {} = True

noTokens :: [Token]
noTokens = [EOF noSourcePos]

-- | Turn the string into a stream of tokens.
tokenize :: SourcePos -> Text -> [Token]
tokenize start = posToken start False
  where
    typeWhitespace :: Bool -> TokenType
    typeWhitespace ws = if ws then WhiteSpaceBefore else NoWhiteSpaceBefore

    posToken :: SourcePos -> Bool -> Text -> [Token]
    posToken pos whitespaceBefore s
      | not (Text.null lexem) =
          makeToken lexem pos (typeWhitespace whitespaceBefore) : posToken (advanceAlong pos lexem) False rest
      where (lexem, rest) = Text.span isLexem s

    posToken pos _ s
      | not (Text.null white) = posToken (advanceAlong pos white) True rest
      where (white, rest) = Text.span isSpace s

    posToken pos whitespaceBefore s = case Text.uncons s of
      Nothing -> [EOF pos]
      Just ('#', _) -> makeToken comment pos Comment : posToken (advanceAlong pos comment) whitespaceBefore rest
        where (comment, rest) = Text.break (== '\n') s
      Just (c, cs) -> makeToken (Text.singleton c) pos (typeWhitespace whitespaceBefore) : posToken (advancePos pos c) False cs

isLexem :: Char -> Bool
isLexem c = (isAscii c && isAlphaNum c) || c == '_'

reportComments :: Token -> Maybe Message.Report
reportComments t@(Token _ _ _)
  | properToken t = Nothing
  | otherwise = Just (tokenPos t, Markup.comment1)
reportComments (EOF _) = Nothing

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
isEOF EOF{} = True; isEOF _ = False
