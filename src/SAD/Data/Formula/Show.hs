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

import SAD.Data.Formula.Base
import SAD.Data.VarName
import SAD.Data.Terms
import SAD.Export.Representation (toLazyText, represent)

import Isabelle.Position qualified as Position
import SAD.Helpers


instance Show Formula where
  showsPrec p = showFormula p 0

showFormula :: Int -> Int -> Formula -> ShowS
showFormula p d = dive
  where
    dive (All _ f) = showString "\\<forall>" . showBinder f
    dive (Exi _ f) = showString "\\<exists>" . showBinder f
    dive (Iff f g) = showParen True $ showInfix " \\<Longleftrightarrow> " f g
    dive (Imp f g) = showParen True $ showInfix " \\<Longrightarrow> " f g
    dive (Or  f g) = showParen True $ showInfix " \\<or> " f g
    dive (And f g) = showParen True $ showInfix " \\<and> " f g
    dive (Tag a f) = showParen True $ shows a . showString " \\<Colon> " . dive f
    dive (Not Trm{trmName = TermEquality, trmArgs = [l,r]}) = showInfix " \\<noteq> " l r
    dive (Not f)   = showString "\\<not>" . dive f
    dive Top       = showString "\\<top>"
    dive Bot       = showString "\\<bottom>"
    dive ThisT     = showString "ThisT"

    dive t@Trm{trmName = TermThesis} = showString "thesis"
    dive t@Trm{trmName = TermEquality, trmArgs = [l,r]} = showInfix " = " l r
    dive t@Trm{trmName = TermSymbolic tName, trmArgs = tArgs} = substitute (Text.unpack tName) tArgs p d
    dive t@Trm{trmName = TermThe tName, trmArgs = tArgs} =
          showString ("the" <> Text.unpack tName) . showArguments tArgs
    dive t@Trm{trmName = tName, trmArgs = tArgs} = showString (Text.unpack $ toLazyText $ represent tName) . showArguments tArgs
    dive v@Var{varName = VarConstant s} = showString (Text.unpack s)
    dive v@Var{varName = vName} = showString $ Text.unpack $ toLazyText $ represent vName
    dive Ind {indIndex = i }
      | i < d = showChar 'v' . shows (d - i - 1)
      | otherwise = showChar 'v' . showChar '?' . showString (show i)

    showArguments _ | p == 1 = showString "(...)"
    showArguments ts =
      let showTerm = showFormula (p - 1) d
      in  showArgumentsWith showTerm ts

    showBinder f = showFormula p (d + 1) (Ind 0 Position.none) . showChar '.' .
      showFormula p (d + 1) f

    showInfix operator f g = dive f . showString operator . dive g


showArgumentsWith :: (a -> ShowS) -> [a] -> ShowS
showArgumentsWith _ [] = id
showArgumentsWith showTerm ls = showParen True $ commaSeparated showTerm ls

commaSeparated :: (a -> ShowS) -> [a] -> ShowS
commaSeparated showTerm [] = id
commaSeparated showTerm [t] = showTerm t
commaSeparated showTerm (t:ts) = showTerm t . showChar ',' . commaSeparated showTerm ts

-- | Substitute all @.@ characters in a string by given terms.
substitute :: String -> [Formula] -> Int -> Int -> ShowS
substitute s [] _ _ = showString s
substitute s (t : ts) p d = dec s
  where
    dec ('.' : cs) = showParen (ambig t) (showFormula p d t) . substitute cs ts p d
    dec (c : cs@('.' : _)) | isAsciiLetter c = showChar c . showChar ' ' . dec cs
    dec (c : cs) = showChar c . dec cs
    dec [] = showString ""

    ambig Trm {trmName = TermSymbolic tName} =
      ("." `Text.isPrefixOf` tName && Text.drop 2 tName /= "(.)") ||
      "." `Text.isSuffixOf` tName
    ambig _ = False
