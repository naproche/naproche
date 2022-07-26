{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Tokenization of input.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token
  ( Token (tokenPos, tokenText)
  , Dialect (..)
  , tokensRange
  , showToken
  , isProperToken
  , tokenize
  , reportComments
  , composeTokens
  , isEOF
  , noTokens
  , greek
  ) where

import qualified Isabelle.Position as Position
import qualified Isabelle.Markup as Markup

import Data.Char
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text


data Token = Token
  { tokenText :: Text
  , tokenPos :: Position.T
  , tokenType :: TokenType
  } | EOF { tokenPos :: Position.T }
  deriving (Eq, Ord)

instance Show Token where
  show Token{tokenText = p, tokenPos = s} = show p
  show EOF{} = "EOF"

data TokenType = NoWhiteSpaceBefore | WhiteSpaceBefore | Comment deriving (Eq, Ord, Show)

-- If at some point one uses a more powerful parser for tokenizing, this should be much
-- less messy.
-- | Indicates whether the tokenizer is currently inside a forthel env.
data TexState = InsideForthelEnv | OutsideForthelEnv deriving (Eq)

makeTokenRange :: Text -> Position.Range -> TokenType -> Token
makeTokenRange text range = Token text (Position.range_position range)

makeToken :: Text -> Position.T -> TokenType -> Token
makeToken text pos = makeTokenRange text (pos, Position.symbol_explode text pos)

tokenEndPos :: Token -> Position.T
tokenEndPos tok@Token{} = Position.symbol_explode (tokenText tok) (tokenPos tok)
tokenEndPos tok@EOF{} = tokenPos tok

-- | The range in which the tokens lie.
tokensRange :: [Token] -> Position.Range
tokensRange [] = Position.no_range
tokensRange toks = Position.range (tokenPos $ head toks, tokenEndPos $ last toks)

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
noTokens = [EOF Position.none]

data Dialect = FTL | TEX

isLexeme :: Char -> Bool
isLexeme c = isAscii c && isAlphaNum c


tokenize :: Dialect -> Position.T -> Text -> [Token]

-- Tokenize an FTL document
tokenize FTL startPos = procToken startPos NoWhiteSpaceBefore
  where
    -- Process a token
    procToken :: Position.T -> TokenType -> Text -> [Token]
    -- Process alphanumeric token
    procToken currentPos whitespaceBefore remainingText
      | not (Text.null lexeme) = tok:toks
      where
        (lexeme, rest) = Text.span isLexeme remainingText
        tok  = makeToken lexeme currentPos whitespaceBefore
        toks = procToken (Position.symbol_explode lexeme currentPos) NoWhiteSpaceBefore rest
    -- Process whitespace
    procToken currentPos _ remainingText
      | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace remainingText
        toks = procToken (Position.symbol_explode white currentPos) WhiteSpaceBefore rest
    -- Process EOF, comment or symbolic token
    procToken currentPos whitespaceBefore remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> [EOF currentPos]
        -- Comment
        Just ('#', _) -> tok:toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            tok  = makeToken comment currentPos Comment
            toks = procToken (Position.symbol_explode comment currentPos) whitespaceBefore rest
        -- Symbolic token
        Just (c, cs) -> tok:toks
          where
            text = Text.singleton c
            tok  = makeToken text currentPos whitespaceBefore
            toks = procToken (Position.symbol_explode text currentPos) NoWhiteSpaceBefore cs

-- Tokenize an FTL-TeX document
tokenize TEX startPos = procToken OutsideForthelEnv startPos NoWhiteSpaceBefore
  where
    -- Process a token
    procToken :: TexState -> Position.T -> TokenType -> Text -> [Token]
    -- When outside a forthel environment, ignore anything till the next
    -- occurence of "\begin{forthel}" and then switch to 'InsideForthelEnv' mode
    -- TODO: Handle commented "\begin{forthel}" expressions
    procToken OutsideForthelEnv currentPos _ remainingText = toks
      where
        (ignoredText, rest) = Text.breakOn "\\begin{forthel}" remainingText
        newPos = Position.symbol_explode (ignoredText <> "\\begin{forthel}") currentPos
        toks = procToken InsideForthelEnv newPos WhiteSpaceBefore $ Text.drop (Text.length "\\begin{forthel}") rest
    -- When we reach an "\end{forthel}" expression inside a forthen environment,
    -- switch to 'OutsideForthelEnv' mode
    procToken InsideForthelEnv currentPos _ remainingText
      | start == "\\end{forthel}" = toks
      where
        (start, rest) = Text.splitAt (Text.length "\\end{forthel}") remainingText
        toks = procToken OutsideForthelEnv (Position.symbol_explode start currentPos) WhiteSpaceBefore rest
    -- Process alphanumeric token
    procToken InsideForthelEnv currentPos whitespaceBefore remainingText
      | not (Text.null lexeme) = tok:toks
      where
        (lexeme, rest) = Text.span isLexeme remainingText
        tok  = makeToken lexeme currentPos whitespaceBefore
        toks = procToken InsideForthelEnv (Position.symbol_explode lexeme currentPos) NoWhiteSpaceBefore rest
    -- Process whitespace
    procToken InsideForthelEnv currentPos _ remainingText
      | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace remainingText
        toks = procToken InsideForthelEnv (Position.symbol_explode white currentPos) WhiteSpaceBefore rest
    -- Process line break
    procToken InsideForthelEnv currentPos _ remainingText
      | head == "\\\\" = toks
      where
        (head, rest) = Text.splitAt (Text.length "\\\\") remainingText
        toks = procToken InsideForthelEnv (Position.symbol_explode head currentPos) WhiteSpaceBefore rest
    -- Display style math mode delimiters
    procToken InsideForthelEnv currentPos _ remainingText
      | head `elem` ["\\[", "\\]"] = toks
      where
        (head, rest) = Text.splitAt 2 remainingText
        toks = procToken InsideForthelEnv (Position.symbol_explode head currentPos) WhiteSpaceBefore rest
    -- Process non-alphanumeric symbol or EOF
    procToken InsideForthelEnv currentPos whitespaceBefore remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> [EOF currentPos]
        -- Inline math mode delimiter
        Just ('$', rest) -> procToken InsideForthelEnv (Position.symbol_explode_string "$" currentPos) WhiteSpaceBefore rest
        -- Comment
        Just ('%', _) -> tok:toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            tok  = makeToken comment currentPos Comment
            toks = procToken InsideForthelEnv (Position.symbol_explode comment currentPos) whitespaceBefore rest
        -- Escaped special character
        Just ('\\', rest)
          | Text.head rest `elem` ['{', '}'] ->
            procToken InsideForthelEnv (Position.symbol_explode_string "\\" currentPos) WhiteSpaceBefore rest
        -- TeX command
        Just ('\\', rest) -> newToks ++ toks
          where
            (name, rest') = Text.span isAlpha rest
            newPos = Position.symbol_explode (Text.cons '\\' name) currentPos
            newToks = expandTexCmd name (currentPos, newPos) whitespaceBefore
            toks = procToken InsideForthelEnv newPos WhiteSpaceBefore rest'
        -- Symbolic token
        Just (c, cs) -> tok:toks
          where
            text = Text.singleton c
            tok  = makeToken text currentPos whitespaceBefore
            toks = procToken InsideForthelEnv (Position.symbol_explode text currentPos) NoWhiteSpaceBefore cs


expandTexCmd :: Text -> Position.Range -> TokenType -> [Token]
-- Logical symbols
expandTexCmd "wedge" range whiteSpaceBefore = makeSymbolTokens ["/","\\"] range whiteSpaceBefore
expandTexCmd "vee" range whiteSpaceBefore = makeSymbolTokens ["\\","/"] range whiteSpaceBefore
expandTexCmd "implies" range whiteSpaceBefore = makeSymbolTokens ["=",">"] range whiteSpaceBefore
expandTexCmd "iff" range whiteSpaceBefore = makeSymbolTokens ["<", "=",">"] range whiteSpaceBefore
expandTexCmd "forall" range whiteSpaceBefore = [makeTokenRange "forall" range whiteSpaceBefore]
expandTexCmd "exists" range whiteSpaceBefore = [makeTokenRange "exists" range whiteSpaceBefore]
-- Special commands
expandTexCmd "mid" range whiteSpaceBefore = [makeTokenRange "|" range whiteSpaceBefore]
expandTexCmd "rightarrow" range whiteSpaceBefore = makeSymbolTokens ["-",">"] range whiteSpaceBefore
expandTexCmd "fun" range whiteSpaceBefore = [makeTokenRange "\\" range whiteSpaceBefore]
-- Grouping commands (simply tokenize away "\left", "\middle" and "\right")
expandTexCmd "left" range whiteSpaceBefore = []
expandTexCmd "middle" range whiteSpaceBefore = []
expandTexCmd "right" range whiteSpaceBefore = []

-- All tokens starting with `\` are treated as symbols by the parser. But there are tex commands,
-- that we don't want to treat as symbols in our patterns, for example greek letters. Thus we expand this fixed
-- list of tex commands here so that they don't use `\`. Note that the fact that this is designed this way makes
-- it conceptually impossible for the user to configure which tex commands are treated as words on the fly.

-- Tex words
expandTexCmd s range whiteSpaceBefore | s `elem` greek = [makeTokenRange ("tex" <> s) range whiteSpaceBefore]
-- If this is not a predefined command to be expanded, just leave the backslash so that it gets treated as a symbol.
expandTexCmd s range whiteSpaceBefore = [makeTokenRange (Text.cons '\\' s) range whiteSpaceBefore]

greek :: [Text]
greek = lowerGreek ++ varGreek ++ upperGreek

lowerGreek :: [Text]
lowerGreek = [
    "alpha"
  , "beta"
  , "gamma"
  , "delta"
  , "epsilon"
  , "zeta"
  , "eta"
  , "theta"
  , "iota"
  , "kappa"
  , "lambda"
  , "mu"
  , "nu"
  , "xi"
  , "omicron"
  , "pi"
  , "rho"
  , "sigma"
  , "tau"
  , "upsilon"
  , "phi"
  , "chi"
  , "psi"
  , "omega"
  ]

varGreek :: [Text]
varGreek = [
    "varbeta"
  , "varepsilon"
  , "vartheta"
  , "varkappa"
  , "varpi"
  , "varvarpi"
  , "varrho"
  , "varvarrho"
  , "varsigma"
  , "varphi"
  ]

upperGreek :: [Text]
upperGreek = [
    "Gamma"
  , "Delta"
  , "Theta"
  , "Lambda"
  , "Xi"
  , "Pi"
  , "Sigma"
  , "Upsilon"
  , "Phi"
  , "Psi"
  , "Omega"
  ]

makeSymbolTokens :: [Text] -> Position.Range -> TokenType -> [Token]
makeSymbolTokens (s:symbols) range whiteSpaceBefore =
  makeTokenRange s range whiteSpaceBefore : makeSymbolTokens symbols range NoWhiteSpaceBefore
makeSymbolTokens [] _ _ = []

reportComments :: Token -> Maybe Position.Report
reportComments t@Token{}
  | isProperToken t = Nothing
  | otherwise = Just (tokenPos t, Markup.comment1)
reportComments EOF{} = Nothing

-- | Append tokens separated by a single space if they were separated
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
