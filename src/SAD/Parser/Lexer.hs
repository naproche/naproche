-- |
-- Module      : SAD.Parser.Lexer
-- Copyright   : (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Generic lexing setup

{-# LANGUAGE MultiParamTypeClasses #-}

module SAD.Parser.Lexer where

import FTLex.Position qualified as Pos
import FTLex.Message qualified as Msg
import Data.Text (Text)

import SAD.Core.Message qualified as Message

import Isabelle.Position qualified as Position
import Isabelle.Library qualified as Library
import FTLex.Position (noPos)


-- * PIDE Setup

instance Pos.Pos Position.T where
  noPos :: Position.T
  noPos = Position.none

  getNextPos :: Text -> Position.T -> Position.T
  getNextPos = Position.symbol_explode

  getPosOf :: Text -> Position.T -> Position.T
  getPosOf text pos =
    let newPos = Position.symbol_explode text pos
    in Position.range_position (pos, newPos)

  showPos :: Position.T -> Text
  showPos = Library.make_text . Position.here


instance Msg.Msg Position.T IO where
  errorLexer :: Position.T -> Text -> IO a
  errorLexer = Message.errorLexer
