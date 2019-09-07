{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Tokenization of input.
-}

{-# LANGUAGE NamedFieldPuns #-}

module SAD.Parser.Token
  ( Token (tokenPos, tokenText),
    tokenEndPos,
    tokensRange,
    showToken,
    properToken,
    tokenize,
    tokenReports,
    composeTokens,
    isEOF,
    noTokens)
  where

import Data.Char
import Data.List

import SAD.Core.SourcePos
import qualified SAD.Core.Message as Message
import qualified Isabelle.Markup as Markup


data Token =
  Token {
    tokenText :: String,
    tokenPos :: SourcePos,
    tokenWhiteSpace :: Bool,
    tokenProper :: Bool} |
  EOF {tokenPos :: SourcePos}

makeToken :: String -> SourcePos -> Bool -> Bool -> Token
makeToken s pos whitespaceBefore proper =
  Token s (rangePos (SourceRange pos (advanceAlong pos s))) whitespaceBefore proper

tokenEndPos :: Token -> SourcePos
tokenEndPos tok@Token{} = advanceAlong (tokenPos tok) (tokenText tok)
tokenEndPos tok@EOF {} = tokenPos tok

tokensRange :: [Token] -> SourceRange
tokensRange toks =
  if null toks then noRange
  else makeRange (tokenPos $ head toks, tokenEndPos $ last toks)

showToken :: Token -> String
showToken t@Token{} = tokenText t
showToken EOF{} = "end of input"

properToken :: Token -> Bool
properToken Token {tokenProper} = tokenProper
properToken EOF {} = True

noTokens :: [Token]
noTokens = [EOF noPos]


-- tokenize

tokenize :: SourcePos -> String -> [Token]
tokenize start = posToken start False
  where
    posToken pos whitespaceBefore s
      | not (null lexem) =
          makeToken lexem pos whitespaceBefore True : posToken (advanceAlong pos lexem) False rest
      where (lexem, rest) = span isLexem s

    posToken pos _ s
      | not (null white) = posToken (advanceAlong pos white) True rest
      where (white, rest) = span isSpace s

    posToken pos whitespaceBefore s@('#':_) =
      makeToken comment pos False False : posToken (advanceAlong pos comment) whitespaceBefore rest
      where (comment, rest) = break (== '\n') s

    posToken pos whitespaceBefore (c:cs) =
      makeToken [c] pos whitespaceBefore True : posToken (advancePos pos c) False cs

    posToken pos _ _ = [EOF pos]

isLexem :: Char -> Bool
isLexem c = (isAscii c && isAlphaNum c) || c == '_'


-- markup reports

tokenReports :: Token -> [Message.Report]
tokenReports Token {tokenPos = pos, tokenProper} =
  if tokenProper then []
  else [(pos, Markup.comment1)]
tokenReports _ = []


-- useful functions

composeTokens :: [Token] -> String
composeTokens [] = ""
composeTokens (t:ts) =
  let whitespaceBefore = if tokenWhiteSpace t then " " else ""
  in  whitespaceBefore ++ showToken t ++ composeTokens ts

isEOF :: Token -> Bool
isEOF EOF{} = True; isEOF _ = False




-- Show instances

instance Show Token where
  showsPrec _ (Token s p _ _) = showString s . shows p
  showsPrec _ _ = showString ""
