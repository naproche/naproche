-- |
-- Module      : SAD.Data.Formula.Show
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
-- License     : GPL-3
--
-- Show instance for formulas.


{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Formula.Show () where

import Data.Text.Lazy qualified as Text
import Data.List qualified as List

import SAD.Data.Formula.Base
import SAD.Data.VarName
import SAD.Data.Terms
import SAD.Export.Representation (toLazyText, represent)

import Isabelle.Position qualified as Position
import SAD.Helpers


instance Show Formula where
  show :: Formula -> String
  show = showFormula 0

showFormula :: Int -> Formula -> String
showFormula d = dive
  where
    dive (All _ f) = showBinder d "\\<forall>" f
    dive (Exi _ f) = showBinder d "\\<exists>" f
    dive (Iff f g) = "(" ++ dive f ++ " \\<Longleftrightarrow> " ++ dive g ++ ")"
    dive (Imp f g) = "(" ++ dive f ++ " \\<Longrightarrow> " ++ dive g ++ ")"
    dive (Or  f g) = "(" ++ dive f ++ " \\<or> " ++ dive g ++ ")"
    dive (And f g) = "(" ++ dive f ++ " \\<and> " ++ dive g ++ ")"
    dive (Tag a f) = "(" ++ show a ++ " \\<Colon> " ++ dive f ++ ")"
    dive (Not Trm{trmName = TermEquality, trmArgs = [l,r]}) = dive l ++ " \\<noteq> " ++ dive r
    dive (Not f) = "\\<not>" ++ dive f
    dive Top = "\\<top>"
    dive Bot = "\\<bottom>"
    dive ThisT = "ThisT"
    dive Trm{trmName = TermThesis} = "thesis"
    dive Trm{trmName = TermEquality, trmArgs = [l,r]} = dive l ++ " = " ++ dive r
    dive Trm{trmName = TermSymbolic tName, trmArgs = tArgs} = substitute (Text.unpack tName) tArgs d
    dive Trm{trmName = tName, trmArgs = tArgs} = Text.unpack (toLazyText (represent tName)) ++ showArguments d tArgs
    dive Var{varName = VarConstant s} = Text.unpack s
    dive Var{varName = vName} = Text.unpack $ toLazyText $ represent vName
    dive Ind {indIndex = i }
      | i < d = "v" ++ show (d - i - 1)
      | otherwise = "v?" ++ show i

-- | Show the arguments (given as a list of formulas) of a term up to a nesting
-- depth of 5.
showArguments :: Int -> [Formula] -> String
showArguments _ [] = ""
showArguments d terms =
  let showTerm = showFormula d
  in "(" ++ List.intercalate "," (map showTerm terms) ++ ")"

-- | Show a variable binder together with the variable it binds and the formula
-- in which it is bound.
showBinder :: Int -> String -> Formula -> String
showBinder d binder formula = binder ++ showFormula (d + 1) (Ind 0 Position.none)
  ++ "." ++ showFormula (d + 1) formula

-- | Substitute all @.@ characters in a string by given terms.
substitute :: String -> [Formula] -> Int -> String
substitute s [] _ = s
substitute s (t : ts) d = dec s
  where
    dec ('.' : cs) = parenIf (ambig t) (showFormula d t) ++ substitute cs ts d
    dec (c : cs@('.' : _)) | isAsciiLetter c = c : " " ++ dec cs
    dec (c : cs) = c : dec cs
    dec [] = ""

    ambig Trm {trmName = TermSymbolic tName} =
      ("." `Text.isPrefixOf` tName && Text.drop 2 tName /= "(.)") ||
      "." `Text.isSuffixOf` tName
    ambig _ = False
