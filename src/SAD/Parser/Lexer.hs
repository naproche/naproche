-- |
-- Authors: Marcel Schütz (2024)
--
-- Lexing

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SAD.Parser.Lexer (
  PIDE_Pos(..),
  fromPIDEPos,
  lexFtl,
  lexTex
) where

import FTLex.Ftl qualified as Ftl
import FTLex.Tex qualified as Tex
import FTLex.Base
import FTLex.Position qualified as Pos
import FTLex.Message qualified as Msg
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8, decodeUtf8)
import Data.Set qualified as Set

import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position
import Isabelle.Bytes qualified as Bytes


-- * PIDE Setup

newtype PIDE_Pos = PIDE_Pos Position.T deriving (Eq, Ord)

fromPIDEPos :: PIDE_Pos -> Position.T
fromPIDEPos (PIDE_Pos pos) = pos


instance Pos.Pos PIDE_Pos where
  noPos :: PIDE_Pos
  noPos = PIDE_Pos Position.none

  getNextPos :: Text -> PIDE_Pos -> PIDE_Pos
  getNextPos text (PIDE_Pos pos) =
    PIDE_Pos $ Position.symbol_explode text pos

  getPosOf :: Text -> PIDE_Pos -> PIDE_Pos
  getPosOf text (PIDE_Pos pos) =
    let newPos = Position.symbol_explode text pos
    in PIDE_Pos $ Position.range_position (pos, newPos)

  showPos :: PIDE_Pos -> Text
  showPos (PIDE_Pos pos) = decodeUtf8 . Bytes.unmake . Position.here $ pos


instance Msg.Msg PIDE_Pos IO where
  errorLexer :: PIDE_Pos -> Text -> IO a
  errorLexer (PIDE_Pos pos) = Message.errorLexer pos


-- * FTL

-- | @lexFtl pos text@ lexes an FTL document @text@ starting at position @pos@
-- in the document.
lexFtl :: PIDE_Pos -> Text -> IO [Ftl.Lexeme PIDE_Pos]
lexFtl pos text = Ftl.runLexer pos (encodeUtf8 text) UTF8 (Ftl.initState pos blocks) LF
  where
    blocks = Set.fromList [BasicLatin, Latin1Supplement]


-- * TeX

-- | @lexTex pos text@ lexes a TEX document @text@ starting at position @pos@
-- in the document.
lexTex :: PIDE_Pos -> Text -> IO [Tex.Lexeme PIDE_Pos]
lexTex pos text = Tex.runLexer pos (encodeUtf8 text) UTF8 (Tex.initState pos blocks) LF
  where
    blocks = Set.fromList [BasicLatin, Latin1Supplement]
