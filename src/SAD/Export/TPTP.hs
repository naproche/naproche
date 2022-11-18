-- |
-- Authors: Andrei Paskevich (2001 - 2008),
--          Steffen Frerix (2017 - 2018)
--
--Print proof task in TPTP syntax.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Export.TPTP (output) where

import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text
import Data.Text.Lazy.Builder (Builder)
import qualified Data.Text.Lazy.Builder as Builder

import SAD.Data.Formula (Formula(..), showTrName, TermName(..))
import SAD.Data.Text.Block (Block(Block))
import qualified SAD.Data.Text.Block as Block
import SAD.Data.Text.Context (Context(..))
import SAD.Export.Representation

import qualified Isabelle.Position as Position
import Isabelle.Library

import Naproche.TPTP (atomic_word)


output :: [Context] -> Context -> Text
output contexts goal = toLazyText $
  mconcat (map (tptpForm ",hypothesis,") $ reverse contexts)
  <> tptpForm ",conjecture," goal

-- Formula print
tptpForm :: Builder -> Context -> Builder
tptpForm s (Context fr (Block { Block.name = m } : _) _) =
  "fof(m"
  <> (if Text.null m then "_" else Builder.fromLazyText m)
  <> s <> tptpTerm 0 fr <> ").\n"
tptpForm _ _ = ""

tptpName :: Formula -> Builder
tptpName = Builder.fromText . make_text . atomic_word . make_bytes . showTrName

tptpTerm :: Int -> Formula -> Builder
tptpTerm d = term
  where
    term (All _ f)  = buildParens $ " ! " <> binder f
    term (Exi _ f)  = buildParens $ " ? " <> binder f
    term (Iff f g)  = sinfix " <=> " f g
    term (Imp f g)  = sinfix " => " f g
    term (Or  f g)  = sinfix " | " f g
    term (And f g)  = sinfix " & " f g
    term (Tag _ f)  = term f
    term (Not f)    = buildParens $ " ~ " <> term f
    term Top        = "$true"
    term Bot        = "$false"
    term t@Trm {trmName = TermEquality} = let [l, r] = trmArgs t in sinfix " = " l r
    term t@Trm {}   = tptpName t <> buildArgumentsWith term (trmArgs t)
    term v@Var {}   = tptpName v
    term i@Ind {}   = "W" <> Builder.fromString (show (d - 1 - indIndex i))
    term ThisT      = error "SAD.Export.TPTP: Didn't expect ThisT here"

    sinfix o f g  = buildParens $ term f <> o <> term g

    binder f  = "[" <> tptpTerm (d + 1) (Ind 0 Position.none) <> "] : " <> tptpTerm (d + 1) f
