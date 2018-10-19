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

import Alice.Parser.Position

data Token = Token {showToken :: String, tokenPos :: SourcePos,
                    tokenWhiteSpace :: Bool}

tokenize :: SourceName -> String -> [Token]
tokenize name = posToken (1,1) False
  where
    posToken p@(ln,cl) ws s
      | not (null lx) =
          Token lx (newP p) ws : posToken (ln, cl + length lx) False rs
      where
        (lx,rs) = span isLexem s

    posToken p _ s
      | not (null wh) = posToken (nextPos p wh) True rs
      where
        (wh,rs) = span isSpace s
        nextPos p [] = p
        nextPos (ln, cl) (c:cs) | isNLine c = nextPos (succ ln, 1) cs
                                | otherwise = nextPos (ln, succ cl) cs

    posToken p ws ('#' : rs) = posToken p ws $ snd $ break isNLine rs
    posToken p@(ln, cl) ws (c:cs) =
      Token [c] (newP p) ws : posToken (ln, succ cl) False cs
    posToken _ _ _         = []

    newP (ln, cl) = newPos name ln cl

isLexem :: Char -> Bool
isLexem c = isAscii c && isAlphaNum c || c == '_'

isNLine :: Char -> Bool
isNLine c = c == '\n'

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
