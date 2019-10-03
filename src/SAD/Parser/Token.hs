{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Tokenization of input.
-}

{-# LANGUAGE NamedFieldPuns #-}

module SAD.Parser.Token
  ( Token (tokenPos, tokenText),
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
import qualified SAD.Core.Message as Message
import qualified Isabelle.Markup as Markup


data Token = Token
  { tokenText :: String
  , tokenPos :: SourcePos
  , tokenType :: TokenType
  } | EOF { tokenPos :: SourcePos }
  deriving (Eq, Ord)

instance Show Token where
  show (Token p s _) = show s ++ show p
  show (EOF _) = "EOF"

data TokenType = NoWhiteSpaceBefore | WhiteSpaceBefore | Comment deriving (Eq, Ord, Show)

-- | Make a token with @s@ as @tokenText@ and the range from @p@ to the end of @s@.
makeToken :: String -> SourcePos -> TokenType -> Token
makeToken s pos = Token s (rangePos (SourceRange pos (pos `advanceAlong` s)))

tokenEndPos :: Token -> SourcePos
tokenEndPos tok@Token{} = tokenPos tok `advanceAlong` tokenText tok
tokenEndPos tok@EOF {} = tokenPos tok

-- | The range in which the tokens lie.
tokensRange :: [Token] -> SourceRange
tokensRange [] = noRange
tokensRange toks = makeRange (tokenPos $ head toks, tokenEndPos $ last toks)

-- | Return the @tokenText@ or "end of input" if the token is @EOF@.
showToken :: Token -> String
showToken t@Token{} = tokenText t
showToken EOF{} = "end of input"

properToken :: Token -> Bool
properToken t@(Token _ _ _) = case tokenType t of
  NoWhiteSpaceBefore -> True
  WhiteSpaceBefore -> True
  Comment -> False
properToken EOF {} = True

noTokens :: [Token]
noTokens = [EOF noSourcePos]

-- | Turn the string into a stream of tokens.
tokenize :: SourcePos -> String -> [Token]
tokenize start = posToken start False
  where
    typeWhitespace :: Bool -> TokenType
    typeWhitespace ws = if ws then WhiteSpaceBefore else NoWhiteSpaceBefore

    posToken pos whitespaceBefore s
      | not (null lexem) =
          makeToken lexem pos (typeWhitespace whitespaceBefore) : posToken (advanceAlong pos lexem) False rest
      where (lexem, rest) = span isLexem s

    posToken pos _ s
      | not (null white) = posToken (advanceAlong pos white) True rest
      where (white, rest) = span isSpace s

    posToken pos whitespaceBefore s@('#':_) =
      makeToken comment pos Comment : posToken (advanceAlong pos comment) whitespaceBefore rest
      where (comment, rest) = break (== '\n') s

    posToken pos whitespaceBefore (c:cs) =
      makeToken [c] pos (typeWhitespace whitespaceBefore) : posToken (advancePos pos c) False cs

    posToken pos _ [] = [EOF pos]

isLexem :: Char -> Bool
isLexem c = (isAscii c && isAlphaNum c) || c == '_'

reportComments :: Token -> Maybe Message.Report
reportComments t@(Token _ _ _)
  | properToken t = Nothing
  | otherwise = Just (tokenPos t, Markup.comment1)
reportComments (EOF _) = Nothing

-- | Append tokens seperated by a single space if they were seperated
-- by whitespace before.
composeTokens :: [Token] -> String
composeTokens [] = ""
composeTokens (t:ts) =
  let whitespaceBefore = if tokenType t == WhiteSpaceBefore then " " else ""
  in  whitespaceBefore ++ showToken t ++ composeTokens ts

isEOF :: Token -> Bool
isEOF EOF{} = True; isEOF _ = False
