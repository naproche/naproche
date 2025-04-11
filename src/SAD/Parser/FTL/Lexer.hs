-- |
-- Module      : SAD.Parser.FTL.Lexer
-- Copyright   : (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Lexing FTL documents

module SAD.Parser.FTL.Lexer (
  Lexeme,
  lex,
  renderLexemes
) where

import Prelude hiding (lex)
import Data.Text (Text)
import Data.List (intercalate)
import FTLex.Ftl qualified as FTL

import SAD.Parser.Lexer
import SAD.Helpers (failureMessage)

import Isabelle.Position qualified as Position
import Isabelle.Bytes qualified as Bytes
import Isabelle.Library qualified as Library


type Lexeme = FTL.Lexeme Position.T

-- | @lex pos text@ lexes an FTL document @text@ with initial position @pos@.
lex :: Position.T -> Bytes.Bytes -> IO [Lexeme]
lex pos bytes = do
  let text = Library.make_text bytes
  FTL.runLexer pos text (FTL.initState pos)

-- | Render a list of lexemes.
renderLexemes :: [Lexeme] -> String
renderLexemes tokens = intercalate "\n" $ map renderLexeme tokens

-- | Render a lexeme.
renderLexeme :: Lexeme -> String
renderLexeme (FTL.Symbol content sourceText sourcePos) =
  "Symbol:\n" ++
  renderContent content ++ "\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos
renderLexeme (FTL.Word content sourceText sourcePos) =
  "Word:\n" ++
  renderContent content ++ "\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos
renderLexeme (FTL.Space sourceText sourcePos) =
  "Space:\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos
renderLexeme (FTL.Comment content sourceText sourcePos) =
  "Comment:\n" ++
  renderContent content ++ "\n" ++
  renderSourceText sourceText ++ "\n" ++
  renderPosition sourcePos
renderLexeme (FTL.IsabelleSymbol content sourceText sourcePos) =
  "Isabelle symbol:\n" ++
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
  "    Line: " ++ maybe (failureMessage "SAD.Parser.FTL.Lexer.renderLexeme" "Unknown line") show (Position.line_of pos) ++ "\n" ++
  "    Column: " ++ maybe (failureMessage "SAD.Parser.FTL.Lexer.renderLexeme" "Unknown column") show (Position.column_of pos) ++ "\n" ++
  "    Offset: " ++ maybe (failureMessage "SAD.Parser.FTL.Lexer.renderLexeme" "Unknown offset") show (Position.offset_of pos) ++ "\n" ++
  "    End-Offset: " ++ maybe (failureMessage "SAD.Parser.FTL.Lexer.renderLexeme" "Unknown end-offset") show (Position.end_offset_of pos)
