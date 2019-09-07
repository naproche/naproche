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
    tokenReports,
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

makeToken :: String -> SourcePos -> TokenType -> Token
makeToken s pos = Token s (rangePos (SourceRange pos (advanceAlong pos s)))

tokenEndPos :: Token -> SourcePos
tokenEndPos tok@Token{} = tokenPos tok `advanceAlong` tokenText tok
tokenEndPos tok@EOF {} = tokenPos tok

tokensRange :: [Token] -> SourceRange
tokensRange [] = noRange
tokensRange toks = makeRange (tokenPos $ head toks, tokenEndPos $ last toks)

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

    posToken pos _ _ = [EOF pos]

isLexem :: Char -> Bool
isLexem c = (isAscii c && isAlphaNum c) || c == '_'

tokenReports :: Token -> [Message.Report]
tokenReports t@(Token _ _ _)
  | properToken t = []
  | otherwise = [(tokenPos t, Markup.comment1)]
tokenReports (EOF _) = []

composeTokens :: [Token] -> String
composeTokens [] = ""
composeTokens (t:ts) =
  let whitespaceBefore = if tokenType t == WhiteSpaceBefore then " " else ""
  in  whitespaceBefore ++ showToken t ++ composeTokens ts

isEOF :: Token -> Bool
isEOF EOF{} = True; isEOF _ = False