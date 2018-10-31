{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Tokenization of input.
-}

module Alice.Parser.Token
  ( Token (showToken, tokenPos),
    tokenize,
    nextPos,
    composeToken )
  where

import Data.Char
import Data.List

import Alice.Core.Position

data Token = Token {showToken :: String, tokenPos :: SourcePos,
                    tokenWhiteSpace :: Bool}

makeToken s pos ws =
  Token s (rangePos (pos, advancesPos pos s)) ws

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

    posToken _ _ _ = []

isLexem :: Char -> Bool
isLexem c = isAscii c && isAlphaNum c || c == '_'


-- useful functions

nextPos :: [Token] -> SourcePos
nextPos [] = EOF
nextPos (t:ts) = tokenPos t

composeToken :: [Token] -> String
composeToken [] = ""
composeToken (t:ts) =
  let ws = if tokenWhiteSpace t then " " else ""
  in  ws ++ showToken t ++ composeToken ts




-- Show instances

instance Show Token where
  showsPrec _ (Token s p _) = showString s . shows p
