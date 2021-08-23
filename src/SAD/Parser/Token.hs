{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Tokenization of input.
-}

{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token
  ( Token (tokenPos, tokenText)
  , TexState (InsideForthelEnv, OutsideForthelEnv, TexDisabled)
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
import qualified SAD.Core.Message as Message

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
data TexState = InsideForthelEnv | OutsideForthelEnv | TexDisabled deriving (Eq)

makeTokenRange :: Text -> Position.Range -> TokenType -> Token
makeTokenRange text range = Token text (Position.range_position range)

makeToken :: Text -> Position.T -> TokenType -> Token
makeToken text pos = makeTokenRange text (pos, Position.advance_symbol_explode text pos)

tokenEndPos :: Token -> Position.T
tokenEndPos tok@Token{} = Position.advance_symbol_explode (tokenText tok) (tokenPos tok)
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

-- | @tokenize commentChars start text@ takes a list of characters @commentChars@ to use
-- for comments when used as first character in the line and a @text@ that gets tokenized
-- starting from the @start@ position.
tokenize :: TexState -> Position.T -> Text -> [Token]
tokenize texState start = posToken texState start NoWhiteSpaceBefore
  where
    useTex = texState /= TexDisabled
    isLexeme c = if useTex then isAscii c && isAlphaNum c else (isAscii c && isAlphaNum c) || c == '_'
    -- Activate the tokenizer when '\begin{forthel}' appears.
    posToken :: TexState -> Position.T -> TokenType -> Text -> [Token]
    posToken OutsideForthelEnv pos _ s = toks
      where
        (ignoredText, rest) = Text.breakOn "\\begin{forthel}" s
        newPos = Position.advance_symbol_explode (ignoredText <> "\\begin{forthel}") pos
        toks = posToken InsideForthelEnv newPos WhiteSpaceBefore (Text.drop 15 rest)

    -- Deactivate the tokenizer when '\end{forthel}' appears.
    posToken InsideForthelEnv pos _ s | start == "\\end{forthel}" = toks
      where
        (start,rest) = Text.splitAt 13 s
        toks = posToken OutsideForthelEnv (Position.advance_symbol_explode start pos) WhiteSpaceBefore rest

    -- Make alphanumeric tokens that don't start with whitespace.
    posToken texState pos whitespaceBefore s | not (Text.null lexeme) = tok:toks
      where
        (lexeme, rest) = Text.span isLexeme s
        tok  = makeToken lexeme pos whitespaceBefore
        toks = posToken texState (Position.advance_symbol_explode lexeme pos) NoWhiteSpaceBefore rest

    -- Process whitespace.
    posToken texState pos _ s | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace s
        toks = posToken texState (Position.advance_symbol_explode white pos) WhiteSpaceBefore rest

    -- Process tex whitespace.
    posToken texState pos _ s | useTex && hd == "\\\\" = toks
      where
        (hd, rest) = Text.splitAt 2 s
        toks = posToken texState (Position.advance_symbol_explode_string "\\\\" pos) WhiteSpaceBefore rest

    -- We reuse the pattern parsing for sentences in order to parse LaTeX. Thus we simply tokenize
    -- away math-mode markers like '\[' and '\]'
    posToken texState pos _ s | useTex && hd `elem` ["\\[","\\]"] = toks
      where 
        (hd, rest) = Text.splitAt 2 s
        toks = posToken texState (Position.advance_symbol_explode hd pos) WhiteSpaceBefore rest

    -- Process non-alphanumeric symbol or EOF.
    posToken texState pos whitespaceBefore s = case Text.uncons s of
      Nothing -> [EOF pos]

      -- We expand the `\{` and `\}` tex commands here
      Just ('\\', rest) | Text.head rest `elem` ['{','}'] && useTex ->
            posToken texState (Position.advance_symbol_explode_string "\\" pos) WhiteSpaceBefore rest

      -- We expand alphanumeric tex commands here
      Just ('\\', rest) | useTex -> newToks ++ toks
        where
          (name, rest') = Text.span isAlpha rest
          pos' = Position.advance_symbol_explode (Text.cons '\\' name) pos
          newToks = expandTexCmd name (pos, pos') whitespaceBefore
          toks = posToken texState pos' WhiteSpaceBefore rest'

      -- We reuse the pattern parsing for sentences in order to parse LaTeX. Thus we simply tokenize
      -- away math-mode markers like '$'
      Just ('$', rest) | useTex -> posToken texState (Position.advance_symbol_explode_string "$" pos) WhiteSpaceBefore rest

      -- We also tokenize away quotation marks, because they are intended to be used by the user
      -- as a way to write regular text in math mode. Of course, one needs to appropriately remap
      -- quotation marks in the tex file, see examples/cantor.ftl.tex on how to do this.
      Just ('"', rest) | useTex -> posToken texState (Position.advance_symbol_explode_string "\"" pos) WhiteSpaceBefore rest
      Just (c, _) | if useTex then c == '%' else c == '#' -> tok:toks
        where
          (comment, rest) = Text.break (== '\n') s
          tok  = makeToken comment pos Comment
          toks = posToken texState (Position.advance_symbol_explode comment pos) whitespaceBefore rest
      Just (c, cs) -> tok:toks
        where
          text = Text.singleton c
          tok  = makeToken text pos whitespaceBefore
          toks = posToken texState (Position.advance_symbol_explode text pos) NoWhiteSpaceBefore cs


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

reportComments :: Token -> Maybe Message.Report
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
