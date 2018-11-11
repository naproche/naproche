{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Tokenization of input.
-}

module Alice.Parser.Token
  ( Token (tokenPos),
    showToken,
    tokenize,
    composeToken,
    isEOF,
    noTokens)
  where

import Data.Char
import Data.List

import Alice.Core.Position

data Token =
  Token {
    tokenText :: String,
    tokenPos :: SourcePos,
    tokenWhiteSpace :: Bool} |
  EOF {tokenPos :: SourcePos}

makeToken s pos ws =
  Token s (rangePos (pos, advancesPos pos s)) ws

showToken :: Token -> String
showToken t@Token{} = tokenText t
showToken EOF{} = "end of input"

noTokens :: [Token]
noTokens = [EOF noPos]


tokenize :: SourcePos -> String -> [Token]
tokenize start = posToken start False
  where
    posToken pos ws s
      | not (null lexem) =
          makeToken lexem pos ws : posToken (advancesPos pos lexem) False rest
      where (lexem, rest) = span isLexem s

    posToken pos _ s
      | not (null white) = posToken (advancesPos pos white) True rest
      where (white, rest) = span isSpace s

    posToken pos ws s@('#':_) = posToken (advancesPos pos comment) ws rest
      where (comment, rest) = break (== '\n') s

    posToken pos ws (c:cs) =
      makeToken [c] pos ws : posToken (advancePos pos c) False cs

    posToken pos _ _ = [EOF pos]

isLexem :: Char -> Bool
isLexem c = isAscii c && isAlphaNum c || c == '_'


-- useful functions

composeToken :: [Token] -> String
composeToken [] = ""
composeToken (t:ts) =
  let ws = if tokenWhiteSpace t then " " else ""
  in  ws ++ showToken t ++ composeToken ts

isEOF :: Token -> Bool
isEOF EOF{} = True; isEOF _ = False




-- Show instances

instance Show Token where
  showsPrec _ (Token s p _) = showString s . shows p
  showsPrec _ _ = showString ""
