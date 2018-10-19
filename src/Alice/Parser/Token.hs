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
tokenize name = posToken (initialPos name) False
  where
    posToken p ws s
      | not (null lx) =
          Token lx p ws : posToken (advancesPos p lx) False rs
      where
        (lx,rs) = span isLexem s

    posToken p _ s
      | not (null wh) = posToken (advancesPos p wh) True rs
      where
        (wh,rs) = span isSpace s

    posToken p ws s@('#' : _) = posToken (advancesPos p cs) ws rs
      where
        (cs, rs) = break (== '\n') s
    posToken p ws (c:cs) =
      Token [c] p ws : posToken (advancePos p c) False cs
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
