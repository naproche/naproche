-- |
-- Module      : SAD.Parser.TEX.Lexer
-- Copyright   : (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Lexing FTL-TeX documents

module SAD.Parser.TEX.Lexer (
  Lexeme,
  lex,
  renderLexemes
) where

import Prelude hiding (lex)
import Data.Text (Text)
import Data.List (intercalate)
import FTLex.Tex qualified as TEX

import SAD.Parser.Lexer
import SAD.Helpers (failureMessage)

import Isabelle.Position qualified as Position
import Isabelle.Bytes qualified as Bytes


type Lexeme = TEX.Lexeme Position.T

-- | @lexTex pos text@ lexes a TEX document @text@ with initial position @pos@.
lex :: Position.T -> Bytes.Bytes -> IO [Lexeme]
lex pos bytes = do
  text <- pideDecode bytes
  TEX.runLexer pos text (TEX.initState TEX.FtlTexMode pos)

-- | Render a list of lexemes.
renderLexemes :: [Lexeme] -> String
renderLexemes tokens = intercalate "\n" $ map renderLexeme tokens

-- | Render a lexeme.
renderLexeme :: Lexeme -> String
renderLexeme (TEX.Character content catCode sourceText sourcePos) =
  "Character:\n" ++
  renderContent content ++ "\n" ++
  renderCatCode catCode ++ "\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos
renderLexeme (TEX.ControlWord content sourceText sourcePos) =
  "Control word:\n" ++
  renderContent content ++ "\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos
renderLexeme (TEX.ControlSymbol content sourceText sourcePos) =
  "Control symbol:\n" ++
  renderContent content ++ "\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos
renderLexeme (TEX.ControlSpace sourceText sourcePos) =
  "Control space:\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos
renderLexeme (TEX.Parameter number sourceText sourcePos) =
  "Parameter:\n" ++
  renderContent number ++ "\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos
renderLexeme (TEX.Skipped sourceText sourcePos) =
  "Skipped:\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos
renderLexeme (TEX.Comment content sourceText sourcePos) =
  "Comment:\n" ++
  renderContent content ++ "\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos

-- | Render the content of a lexeme.
renderContent :: Show a => a -> String
renderContent content = "  Content: " ++ show content

-- | Render the source text of a lexeme.
renderSourceText :: Text -> String
renderSourceText text = "  Source text: " ++ show text

-- | Render the source position of a lexeme.
renderPosition :: Position.T -> String
renderPosition pos =
  "  Source position:\n" ++
  "    Line: " ++ maybe (failureMessage "SAD.Parser.TEX.Lexer.renderLexeme" "Unknown line") show (Position.line_of pos) ++ "\n" ++
  "    Column: " ++ maybe (failureMessage "SAD.Parser.TEX.Lexer.renderLexeme" "Unknown column") show (Position.column_of pos) ++ "\n" ++
  "    Offset: " ++ maybe (failureMessage "SAD.Parser.TEX.Lexer.renderLexeme" "Unknown offset") show (Position.offset_of pos) ++ "\n" ++
  "    End-Offset: " ++ maybe (failureMessage "SAD.Parser.TEX.Lexer.renderLexeme" "Unknown end-offset") show (Position.end_offset_of pos)

-- | Render the category code of a character lexeme.
renderCatCode :: TEX.CatCode -> String
renderCatCode catCode = "  Category Code: " ++ render catCode
  where 
    render TEX.EscapeCharCat = "0 (escape character)"
    render TEX.BeginGroupCat = "1 (begin grouping)"
    render TEX.EndGroupCat = "2 (end grouping)"
    render TEX.MathShiftCat = "3 (math shift)"
    render TEX.AlignTabCat = "4 (alignment tab)"
    render TEX.EndOfLineCat = "5 (end of line)"
    render TEX.ParamCharCat = "6 (parameter)"
    render TEX.SuperscriptCat = "7 (superscript)"
    render TEX.SubscriptCat = "8 (subscript)"
    render TEX.IgnoredCat = "9 (ignored)"
    render TEX.SpaceCat = "10 (space)"
    render TEX.LetterCat = "11 (letter)"
    render TEX.OtherCat = "12 (other)"
    render TEX.ActiveCat = "13 (active)"
    render TEX.CommentPrefixCat = "14 (comment prefix)"
    render TEX.InvalidCat = failureMessage "SAD.Parser.TEX.Lexer.renderCatCode" "Invalid character"
    render TEX.UnknownCat = failureMessage "SAD.Parser.TEX.Lexer.renderCatCode" "Unknown character"
