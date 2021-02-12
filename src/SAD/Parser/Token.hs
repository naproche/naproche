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

import SAD.Core.SourcePos
import qualified Isabelle.Markup as Markup
import qualified SAD.Core.Message as Message

import Data.Char
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text


data Token = Token
  { tokenText :: Text
  , tokenPos :: SourcePos
  , tokenType :: TokenType
  } | EOF { tokenPos :: SourcePos }
  deriving (Eq, Ord)

instance Show Token where
  show Token{tokenText = p, tokenPos = s} = show s ++ show p
  show EOF{} = "EOF"

data TokenType = NoWhiteSpaceBefore | WhiteSpaceBefore | Comment deriving (Eq, Ord, Show)

-- If at some point one uses a more powerful parser for tokenizing, this should be much
-- less messy.
-- | Indicates whether the tokenizer is currently inside a forthel env.
data TexState = InsideForthelEnv | OutsideForthelEnv | TexDisabled deriving (Eq)

-- | Make a token with @s@ as @tokenText@ and the range from @p@ to the end of @s@.
makeToken :: Text -> SourcePos -> TokenType -> Token
makeToken s pos = Token s (rangePos (SourceRange pos (pos `advancePos` s)))

tokenEndPos :: Token -> SourcePos
tokenEndPos tok@Token{} = tokenPos tok `advancePos` tokenText tok
tokenEndPos tok@EOF{} = tokenPos tok

-- | The range in which the tokens lie.
tokensRange :: [Token] -> SourceRange
tokensRange [] = noRange
tokensRange toks = makeRange (tokenPos $ head toks, tokenEndPos $ last toks)

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
noTokens = [EOF noSourcePos]

-- | @tokenize commentChars start text@ takes a list of characters @commentChars@ to use
-- for comments when used as first character in the line and a @text@ that gets tokenized
-- starting from the @start@ position.
tokenize :: TexState -> SourcePos -> Text -> [Token]
tokenize texState start = posToken texState start NoWhiteSpaceBefore
  where
    useTex = texState /= TexDisabled
    isLexeme c = if useTex then isAscii c && isAlphaNum c else (isAscii c && isAlphaNum c) || c == '_'
    -- Activate the tokenizer when '\begin{forthel}' appears.
    posToken :: TexState -> SourcePos -> TokenType -> Text -> [Token]
    posToken OutsideForthelEnv pos _ s = toks
      where
        (ignoredText, rest) = Text.breakOn "\\begin{forthel}" s
        newPos = advancePos pos (ignoredText <> "\\begin{forthel}")
        toks = posToken InsideForthelEnv newPos WhiteSpaceBefore (Text.drop 15 rest)

    -- Deactivate the tokenizer when '\end{forthel}' appears.
    posToken InsideForthelEnv pos _ s | start == "\\end{forthel}" = toks
      where
        (start,rest) = Text.splitAt 13 s
        toks = posToken OutsideForthelEnv (advancePos pos start) WhiteSpaceBefore rest

    -- Make alphanumeric tokens that don't start with whitespace.
    posToken texState pos whitespaceBefore s | not (Text.null lexeme) = tok:toks
      where
        (lexeme, rest) = Text.span isLexeme s
        tok  = makeToken lexeme pos whitespaceBefore
        toks = posToken texState (advancePos pos lexeme) NoWhiteSpaceBefore rest

    -- Process whitespace.
    posToken texState pos _ s | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace s
        toks = posToken texState (advancePos pos white) WhiteSpaceBefore rest

    -- Process tex whitespace.
    posToken texState pos _ s | useTex && hd == "\\\\" = toks
      where
        (hd, rest) = Text.splitAt 2 s
        toks = posToken texState (advancePos pos "\\\\") WhiteSpaceBefore rest

    -- Process non-alphanumeric symbol or EOF.
    posToken texState pos whitespaceBefore s = case Text.uncons s of
      Nothing -> [EOF pos]

      -- We expand the `\{` and `\}` tex commands here
      Just ('\\', rest) | Text.head rest `elem` ['{','}'] && useTex ->
            posToken texState (advancePos pos "\\") WhiteSpaceBefore rest

      -- We expand alphanumeric tex commands here
      Just ('\\', rest) | useTex -> newToks ++ toks
        where
          (name, rest') = Text.span isAlpha rest
          newToks = expandTexCmd name pos whitespaceBefore
          toks = posToken texState (advancePos pos (Text.cons '\\' name)) WhiteSpaceBefore rest'

      Just ('$', rest) | useTex -> posToken texState (advancePos pos "$") WhiteSpaceBefore rest

      -- We also tokenize away quotation marks, because they are intended to be used by the user
      -- as a way to write regular text in math mode. Of course, one needs to appropriately remap
      -- quotation marks in the tex file, see examples/cantor.ftl.tex on how to do this.
      Just ('"', rest) | useTex -> posToken texState (advancePos pos "\"") WhiteSpaceBefore rest
      Just (c, _) | if useTex then c == '%' else c == '#' -> tok:toks
        where
          (comment, rest) = Text.break (== '\n') s
          tok  = makeToken comment pos Comment
          toks = posToken texState (advancePos pos comment) whitespaceBefore rest
      Just (c, cs) -> tok:toks
        where
          text = Text.singleton c
          tok  = makeToken text pos whitespaceBefore
          toks = posToken texState (advancePos pos text) NoWhiteSpaceBefore cs


expandTexCmd :: Text -> SourcePos -> TokenType -> [Token]
-- Logical symbols
expandTexCmd "wedge" pos whiteSpaceBefore = makeSymbolTokens ["/","\\"] pos whiteSpaceBefore
expandTexCmd "vee" pos whiteSpaceBefore = makeSymbolTokens ["\\","/"] pos whiteSpaceBefore
expandTexCmd "implies" pos whiteSpaceBefore = makeSymbolTokens ["=",">"] pos whiteSpaceBefore
expandTexCmd "iff" pos whiteSpaceBefore = makeSymbolTokens ["<", "=",">"] pos whiteSpaceBefore
expandTexCmd "forall" pos whiteSpaceBefore = [makeToken "forall" pos whiteSpaceBefore]
expandTexCmd "exists" pos whiteSpaceBefore = [makeToken "exists" pos whiteSpaceBefore]
-- Special commands
expandTexCmd "mid" pos whiteSpaceBefore = [makeToken "|" pos whiteSpaceBefore]
expandTexCmd "rightarrow" pos whiteSpaceBefore = makeSymbolTokens ["-",">"] pos whiteSpaceBefore
expandTexCmd "fun" pos whiteSpaceBefore = [makeToken "\\" pos whiteSpaceBefore]

-- All tokens starting with `\` are treated as symbols by the parser. But there are tex commands,
-- that we don't want to treat as symbols in our patterns, for example greek letters. Thus we expand this fixed
-- list of tex commands here so that they don't use `\`. Note that the fact that this is designed this way makes
-- it conceptually impossible for the user to configure which tex commands are treated as words on the fly.

-- Tex words
expandTexCmd s pos whiteSpaceBefore | s `elem` greek = [makeToken ("tex" <> s) pos whiteSpaceBefore]
-- If this is not a predefined command to be expanded, just leave the backslash so that it gets treated as a symbol.
expandTexCmd s pos whiteSpaceBefore = [makeToken (Text.cons '\\' s) pos whiteSpaceBefore]

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

-- This is only used in `expandTexCmd` and used to apply `makeToken` multiple times, while appropriately
-- advancing the position.
makeSymbolTokens :: [Text] -> SourcePos -> TokenType -> [Token]
makeSymbolTokens (s:symbols) pos whiteSpaceBefore =
  makeToken s pos whiteSpaceBefore : makeSymbolTokens symbols (advancePos pos s) NoWhiteSpaceBefore
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
