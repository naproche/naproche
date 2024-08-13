-- |
-- Module      : SAD.Parser.Token
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix,
--               (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Tokenization of input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Parser.Token (
  -- * Tokens
  Token (tokenPos, tokenText),

  -- * Converting Lexemes to Tokens
  ftlLexemesToTokens,
  texLexemesToTokens,

  -- * Legacy Dependencies
  tokensRange,
  showToken,
  composeTokens,
  isEOF,
  noTokens
) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Control.Monad.Extra (concatMapM)
import FTLex.Ftl qualified as Ftl
import FTLex.Tex qualified as Tex
import Data.List qualified as List

import SAD.Parser.Lexer
import SAD.Core.Message qualified as Message
import SAD.Helpers

import Isabelle.Position qualified as Position
import Isabelle.Markup qualified as Markup


-- * Tokens

-- | A token of a ForTheL text
data Token =
    Token {
      tokenText :: Text
    , tokenPos :: Position.T
    }
  | EOF { tokenPos :: Position.T }
  deriving (Eq, Ord)

instance Show Token where
  show Token{tokenText = p, tokenPos = s} = show p
  show EOF{} = "EOF"


-- * Converting Lexemes to Tokens

-- ** FTL

-- | Convert a list of FTL lexemes to tokens and throw PIDE markup reports for
-- all comments.
ftlLexemesToTokens :: [Ftl.Lexeme PIDE_Pos] -> IO [Token]
ftlLexemesToTokens lexemes = do
  tokens <- concatMapM toTokens lexemes
  return $ tokens ++ [EOF Position.none]
  where
    toTokens (Ftl.Symbol char _ pos) =
      pure [Token (Text.singleton char) (fromPIDEPos pos)]
    toTokens (Ftl.Word text _ pos) =
      pure [Token (Text.fromStrict text) (fromPIDEPos pos)]
    toTokens (Ftl.Space _ _) = pure []
    toTokens (Ftl.Comment _ _ pos) = do
      Message.reports [(fromPIDEPos pos, Markup.comment1)]
      return []


-- ** TeX

data TexState =
    InsideForthelEnv
  | OutsideForthelEnv
  deriving (Eq)

-- | Convert a list of TeX lexemes to tokens and throw PIDE markup reports for
-- all comments.
texLexemesToTokens :: [Tex.Lexeme PIDE_Pos] -> IO [Token]
texLexemesToTokens = procToken OutsideForthelEnv
  where
    procToken :: TexState -> [Tex.Lexeme PIDE_Pos] -> IO [Token]
    procToken OutsideForthelEnv remainingLexemes =
      case remainingLexemes of
        -- EOF:
        [] -> pure [EOF Position.none]
        -- "\begin{forthel}":
        Tex.ControlWord{Tex.ctrlWordContent = "begin"} :
          Tex.Character{Tex.charCatCode = Tex.BeginGroupCat} :
          Tex.Character{Tex.charContent = 'f'} :
          Tex.Character{Tex.charContent = 'o'} :
          Tex.Character{Tex.charContent = 'r'} :
          Tex.Character{Tex.charContent = 't'} :
          Tex.Character{Tex.charContent = 'h'} :
          Tex.Character{Tex.charContent = 'e'} :
          Tex.Character{Tex.charContent = 'l'} :
          Tex.Character{Tex.charCatCode = Tex.EndGroupCat} :
          rest ->
            procToken InsideForthelEnv rest
        -- "\section":
        Tex.ControlWord{Tex.ctrlWordContent = "section", Tex.sourcePos = PIDE_Pos pos} : rest ->
          let
            tokens = pure [Token{tokenText = "\\" <> "section", tokenPos = pos}]
            remainingTokens = procToken OutsideForthelEnv rest
          in liftA2 (++) tokens remainingTokens
        -- Comment:
        Tex.Comment{Tex.sourcePos = PIDE_Pos pos} : rest -> do
          Message.reports [(pos, Markup.comment1)]
          procToken OutsideForthelEnv rest
        -- Anything else:
        _ : rest ->
          procToken OutsideForthelEnv rest
    procToken InsideForthelEnv remainingLexemes =
      case remainingLexemes of
        -- EOF:
        [] -> Message.errorTokenizer Position.none ("File ended with un-closed 'forthel' environment." :: Text)
        -- "\end{forthel}":
        Tex.ControlWord{Tex.ctrlWordContent = "end"} :
          Tex.Character{Tex.charCatCode = Tex.BeginGroupCat} :
          Tex.Character{Tex.charContent = 'f'} :
          Tex.Character{Tex.charContent = 'o'} :
          Tex.Character{Tex.charContent = 'r'} :
          Tex.Character{Tex.charContent = 't'} :
          Tex.Character{Tex.charContent = 'h'} :
          Tex.Character{Tex.charContent = 'e'} :
          Tex.Character{Tex.charContent = 'l'} :
          Tex.Character{Tex.charCatCode = Tex.EndGroupCat} :
          rest ->
            procToken OutsideForthelEnv rest
        -- Comment:
        Tex.Comment{Tex.sourcePos = PIDE_Pos pos} : rest -> do
          Message.reports [(pos, Markup.comment1)]
          procToken InsideForthelEnv rest
        -- Skipped text:
        Tex.Skipped{} : rest ->
          procToken InsideForthelEnv rest
        -- Parameter:
        Tex.Parameter{Tex.sourcePos = PIDE_Pos pos} : _ ->
          Message.errorTokenizer pos ("Parameter inside 'forthel' environment." :: Text)
        -- Control space:
        Tex.ControlSpace{} : rest ->
          procToken InsideForthelEnv rest
        -- Control symbol:
        Tex.ControlSymbol{Tex.ctrlSymbolContent = symbol, Tex.sourcePos = PIDE_Pos pos} : rest ->
          let
            tokens = case symbol of
              '\\' -> pure []
              '[' -> pure []
              ']' -> pure []
              '(' -> pure []
              ')' -> pure []
              '{' -> pure [Token{tokenText = "{", tokenPos = pos}]
              '}' -> pure [Token{tokenText = "}", tokenPos = pos}]
              _ -> pure [Token{tokenText = "\\" <> Text.singleton symbol, tokenPos = pos}]
            remainingTokens = procToken InsideForthelEnv rest
          in liftA2 (++) tokens remainingTokens
        -- Control word:
        Tex.ControlWord{Tex.ctrlWordContent = word, Tex.sourcePos = PIDE_Pos pos} : rest ->
          let
            tokens = case word of
              "left" -> pure []
              "middle" -> pure []
              "right" -> pure []
              "par" -> pure []
              _ -> pure [Token{tokenText = "\\" <> Text.fromStrict word, tokenPos = pos}]
            remainingTokens = procToken InsideForthelEnv rest
          in liftA2 (++) tokens remainingTokens
        -- Character:
        lex@Tex.Character{Tex.charContent = char, Tex.charCatCode = catCode, Tex.sourcePos = PIDE_Pos pos} : rest ->
          if isAsciiAlphaNum char
            then let
                (alphaNums, rest') = List.span isAlphaNumLex (lex : rest)
                tokens = pure [makeAlphaNumToken alphaNums]
                remainingTokens = procToken InsideForthelEnv rest'
              in liftA2 (++) tokens remainingTokens
            else let
                tokens = case catCode of
                  Tex.MathShiftCat -> pure []
                  Tex.EndOfLineCat -> pure []
                  Tex.SpaceCat -> pure []
                  _ -> pure [Token{tokenText = Text.singleton char, tokenPos = pos}]
                remainingTokens = procToken InsideForthelEnv rest
              in liftA2 (++) tokens remainingTokens

    makeAlphaNumToken :: [Tex.Lexeme PIDE_Pos] -> Token
    makeAlphaNumToken alphaNumLexemes =
      let
        text = Text.pack $ map Tex.charContent alphaNumLexemes
        positions = map (fromPIDEPos . Tex.sourcePos) alphaNumLexemes
        lastLexeme = last alphaNumLexemes
        nextPos = Position.symbol_explode (Text.singleton . Tex.charContent $ lastLexeme) (fromPIDEPos . Tex.sourcePos $ lastLexeme)
        pos = Position.range_position (head positions, nextPos)
      in
        Token{tokenText = text, tokenPos = pos}

    isAlphaNumLex :: Tex.Lexeme PIDE_Pos -> Bool
    isAlphaNumLex Tex.Character{Tex.charContent = char} = isAsciiAlphaNum char
    isAlphaNumLex _ = False


-- * Legacy Dependencies

-- Get the end position of a token
tokenEndPos :: Token -> Position.T
tokenEndPos tok@Token{} = Position.symbol_explode (tokenText tok) (tokenPos tok)
tokenEndPos tok@EOF{} = tokenPos tok

-- | The range in which the tokens lie
tokensRange :: [Token] -> Position.Range
tokensRange [] = Position.no_range
tokensRange toks = Position.range (tokenPos $ head toks, tokenEndPos $ last toks)

-- | Print a token
showToken :: Token -> Text
showToken t@Token{} = tokenText t
showToken EOF{} = Text.pack "end of input"

-- | Append tokens separated by a single space if they were separated
-- by whitespace before
composeTokens :: [Token] -> Text
composeTokens = Text.concat . dive
  where
    dive [] = []
    dive [t] = [showToken t]
    dive (t : t' : ts) = if noSpaceBetween t t'
      then showToken t : dive (t' : ts)
      else showToken t : " " : dive (t' : ts)
    noSpaceBetween t t' = case Position.offset_of (tokenPos t) of
        Just n -> case Position.offset_of (tokenPos t') of
          Just m -> n == m + 1
          Nothing -> False
        Nothing -> False

-- | A singleton /end of file/ token, i.e. the result of tokenizing an empty
-- document
noTokens :: [Token]
noTokens = [EOF Position.none]

-- | Determines whether a token is an /end of file/ token
isEOF :: Token -> Bool
isEOF EOF{} = True
isEOF _ = False
