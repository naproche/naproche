-- |
-- Author: Andrei Paskevich (2001 - 2008),
--         Steffen Frerix (2017 - 2018)
--         Marcel Schütz (2024)
--
-- Lexing TEX input.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Lexer.TEX (tokenize) where

import Data.Char
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.Maybe (fromMaybe)

import SAD.Parser.Token (Token(..), TokenType(..), makeToken)
import SAD.Lexer.Primitives

import Isabelle.Position qualified as Position


data ForthelState = InsideForthelEnv | OutsideForthelEnv deriving (Eq)

tokenize :: Position.T -> Text -> [Token]
tokenize startPos = processToken OutsideForthelEnv startPos NoWhiteSpaceBefore
  where
    processToken :: ForthelState -> Position.T -> TokenType -> Text -> [Token]
    -- When outside a forthel environment, ignore anything till the next
    -- occurence of "\begin{forthel}" and then switch to 'InsideForthelEnv' mode
    -- TODO: Handle commented "\begin{forthel}" expressions
    processToken OutsideForthelEnv currentPos _ remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> [EOF currentPos]
        Just ('\\', rest)
          -- Translate "\inputref" commands to "readtex" instructions (TODO: Improve this!):
          | Text.isPrefixOf "inputref[naproche/examples/" rest ->
              let (archive_name, rest') = Text.breakOn "]{" $ fromMaybe "" (Text.stripPrefix "inputref[naproche/examples/" rest)
                  (file_name, _) = Text.breakOn "}" $ fromMaybe "" (Text.stripPrefix "]{" rest')
                  token_text = "\\inputref[naproche/examples/" <> archive_name <> "]{" <> file_name <> "}"
                  newPos = Position.symbol_explode_string (Text.unpack token_text) currentPos
                  read_instruction = [
                      Token "[" Position.none WhiteSpaceBefore,
                      makeToken "readtex" Position.none NoWhiteSpaceBefore,
                      makeToken (archive_name <> "/source/" <> file_name) currentPos WhiteSpaceBefore,
                      makeToken "]" Position.none NoWhiteSpaceBefore
                    ]
                  toks = processToken OutsideForthelEnv newPos WhiteSpaceBefore $ Text.drop (Text.length token_text) remainingText
              in read_instruction ++ toks
          -- Translate "\importmodule" commands to "readtex" instructions (TODO: Improve this!):
          | Text.isPrefixOf "importmodule[naproche/examples/" rest ->
              let (archive_name, rest') = Text.breakOn "]{" $ fromMaybe "" (Text.stripPrefix "importmodule[naproche/examples/" rest)
                  (module_name, _) = Text.breakOn "}" $ fromMaybe "" (Text.stripPrefix "]{" rest')
                  token_text = "\\importmodule[naproche/examples/" <> archive_name <> "]{" <> module_name <> "}"
                  newPos = Position.symbol_explode_string (Text.unpack token_text) currentPos
                  read_instruction = [
                      makeToken "[" Position.none WhiteSpaceBefore,
                      makeToken "readtex" Position.none NoWhiteSpaceBefore,
                      makeToken (archive_name <> "/source/" <> Text.replace "?" "/" module_name <> ".tex") currentPos WhiteSpaceBefore,
                      makeToken "]" Position.none NoWhiteSpaceBefore
                    ]
                  toks = processToken OutsideForthelEnv newPos WhiteSpaceBefore $ Text.drop (Text.length token_text) remainingText
              in read_instruction ++ toks
          -- Translate "\usemodule" commands to "readtex" instructions (TODO: Improve this!):
          | Text.isPrefixOf "usemodule[naproche/examples/" rest ->
              let (archive_name, rest') = Text.breakOn "]{" $ fromMaybe "" (Text.stripPrefix "usemodule[naproche/examples/" rest)
                  (module_name, _) = Text.breakOn "}" $ fromMaybe "" (Text.stripPrefix "]{" rest')
                  token_text = "\\usemodule[naproche/examples/" <> archive_name <> "]{" <> module_name <> "}"
                  newPos = Position.symbol_explode_string (Text.unpack token_text) currentPos
                  read_instruction = [
                      makeToken "[" Position.none WhiteSpaceBefore,
                      makeToken "readtex" Position.none NoWhiteSpaceBefore,
                      makeToken (archive_name <> "/source/" <> Text.replace "?" "/" module_name <> ".tex") currentPos WhiteSpaceBefore,
                      makeToken "]" Position.none NoWhiteSpaceBefore
                    ]
                  toks = processToken OutsideForthelEnv newPos WhiteSpaceBefore $ Text.drop (Text.length token_text) remainingText
              in read_instruction ++ toks
          -- Tokenize the content of a forthel environment:
          | Text.isPrefixOf "begin{forthel}" rest ->
              let newPos = Position.symbol_explode_string "\\begin{forthel}" currentPos
              in processToken InsideForthelEnv newPos NoWhiteSpaceBefore $ Text.drop (Text.length "\\begin{forthel}") remainingText
          -- Tokenize f-environments:
          | Text.isPrefixOf "begin{fsignature}" rest -> tokenizeFEnv "fsignature" remainingText
          | Text.isPrefixOf "begin{fdefinition}" rest -> tokenizeFEnv "fdefinition" remainingText
          | Text.isPrefixOf "begin{faxiom}" rest -> tokenizeFEnv "faxiom" remainingText
          | Text.isPrefixOf "begin{ftheorem}" rest -> tokenizeFEnv "ftheorem" remainingText
          | Text.isPrefixOf "begin{flemma}" rest -> tokenizeFEnv "flemma" remainingText
          | Text.isPrefixOf "begin{fproposition}" rest -> tokenizeFEnv "fproposition" remainingText
          | Text.isPrefixOf "begin{fcorollary}" rest -> tokenizeFEnv "fcorollary" remainingText
          | Text.isPrefixOf "begin{fconvention}" rest -> tokenizeFEnv "fconvention" remainingText
          | Text.isPrefixOf "begin{fsignature*}" rest -> tokenizeFEnv "fsignature*" remainingText
          | Text.isPrefixOf "begin{fdefinition*}" rest -> tokenizeFEnv "fdefinition*" remainingText
          | Text.isPrefixOf "begin{faxiom*}" rest -> tokenizeFEnv "faxiom*" remainingText
          | Text.isPrefixOf "begin{ftheorem*}" rest -> tokenizeFEnv "ftheorem*" remainingText
          | Text.isPrefixOf "begin{flemma*}" rest -> tokenizeFEnv "flemma*" remainingText
          | Text.isPrefixOf "begin{fproposition*}" rest -> tokenizeFEnv "fproposition*" remainingText
          | Text.isPrefixOf "begin{fcorollary*}" rest -> tokenizeFEnv "fcorollary*" remainingText
          | Text.isPrefixOf "begin{fconvention*}" rest -> tokenizeFEnv "fconvention*" remainingText
          | Text.isPrefixOf "begin{fproof}" rest -> tokenizeFEnv "fproof" remainingText
          where
            tokenizeFEnv envname text =
              let (envWithoutEnd,restWithEnvEnd) = Text.breakOn ("\\end{" <> envname <> "}") text
                  env = envWithoutEnd <> "\\end{" <> envname <> "}"
                  rest = Text.drop (Text.length ("\\end{" <> envname <> "}")) restWithEnvEnd
                  -- We tokenize the whole environment (including "begin" and "end" command) as if we were inside a forthel environment:
                  envToks = processToken InsideForthelEnv currentPos NoWhiteSpaceBefore env
                  newPos = Position.symbol_explode env currentPos
                  restToks = processToken OutsideForthelEnv newPos NoWhiteSpaceBefore rest
              in envToks ++ restToks
        -- Ignore comments:
        Just ('%', rest) -> newTok : toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            newTok = makeToken comment currentPos Comment
            newPos = Position.symbol_explode comment currentPos
            toks = processToken OutsideForthelEnv newPos WhiteSpaceBefore rest
        -- Ignore everything else:
        Just (c, rest) -> processToken OutsideForthelEnv (Position.symbol_explode_string [c] currentPos) NoWhiteSpaceBefore rest
    -- When we reach an "\end{forthel}" expression inside a forthen environment,
    -- switch to 'OutsideForthelEnv' mode
    processToken InsideForthelEnv currentPos _ remainingText
      | start == "\\end{forthel}" = toks
      where
        (start, rest) = Text.splitAt (Text.length "\\end{forthel}") remainingText
        newPos = Position.symbol_explode start currentPos
        toks = processToken OutsideForthelEnv newPos WhiteSpaceBefore rest
    -- Process alphanumeric token
    processToken InsideForthelEnv currentPos whitespaceBefore remainingText
      | not (Text.null lexeme) = newTok : toks
      where
        (lexeme, rest) = Text.span isAsciiAlphaNum remainingText
        newPos = Position.symbol_explode lexeme currentPos
        newTok = makeToken lexeme currentPos whitespaceBefore
        toks = processToken InsideForthelEnv newPos NoWhiteSpaceBefore rest
    -- Process whitespace
    processToken InsideForthelEnv currentPos _ remainingText
      | not (Text.null white) = toks
      where
        (white, rest) = Text.span isSpace remainingText
        newPos = Position.symbol_explode white currentPos
        toks = processToken InsideForthelEnv newPos WhiteSpaceBefore rest
    -- Process line break
    processToken InsideForthelEnv currentPos _ remainingText
      | head == "\\\\" = toks
      where
        (head, rest) = Text.splitAt (Text.length "\\\\") remainingText
        newPos = Position.symbol_explode head currentPos
        toks = processToken InsideForthelEnv newPos WhiteSpaceBefore rest
    -- Display style math mode delimiters
    processToken InsideForthelEnv currentPos _ remainingText
      | head `elem` ["\\[", "\\]", "\\(", "\\)"] = toks
      where
        (head, rest) = Text.splitAt 2 remainingText
        newPos = Position.symbol_explode head currentPos
        toks = processToken InsideForthelEnv newPos WhiteSpaceBefore rest
    -- Process non-alphanumeric symbol or EOF
    processToken InsideForthelEnv currentPos whitespaceBefore remainingText =
      case Text.uncons remainingText of
        -- EOF
        Nothing -> []
        -- Inline math mode delimiter
        Just ('$', rest) -> toks
          where
            newPos = Position.symbol_explode_string "$" currentPos
            toks = processToken InsideForthelEnv newPos WhiteSpaceBefore rest
        -- Comment
        Just ('%', _) -> newTok : toks
          where
            (comment, rest) = Text.break (== '\n') remainingText
            newPos = Position.symbol_explode comment currentPos
            newTok = makeToken comment currentPos Comment
            toks = processToken InsideForthelEnv newPos WhiteSpaceBefore rest
        -- Escaped special character
        Just ('\\', rest)
          | Text.head rest `elem` ['{', '}'] -> toks
              where
                newPos = Position.symbol_explode_string "\\" currentPos
                toks = processToken InsideForthelEnv newPos NoWhiteSpaceBefore rest
        -- TeX command
        Just ('\\', rest) -> case name of
          "left" -> toks
          "middle" -> toks
          "right" -> toks
          _ -> newTok : toks
          where
            (name, rest') = Text.span isAlpha rest
            texCommand = Text.cons '\\' name
            newPos = Position.symbol_explode texCommand currentPos
            newTok = makeToken texCommand currentPos whitespaceBefore
            toks = processToken InsideForthelEnv newPos NoWhiteSpaceBefore rest'
        -- Symbolic token
        Just (c, cs) -> newTok : toks
          where
            symbol = Text.singleton c
            newPos = Position.symbol_explode symbol currentPos
            newTok = makeToken symbol currentPos whitespaceBefore
            toks = processToken InsideForthelEnv newPos NoWhiteSpaceBefore cs
