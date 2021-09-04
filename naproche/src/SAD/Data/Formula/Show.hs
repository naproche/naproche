{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Formula.Show (
  showArgumentsWith,
  commaSeparated,
  showFormula,
  showsPrecFormula
  -- also exports show instance for Formula
  )where

import SAD.Data.Formula.Base
import SAD.Data.Terms
import SAD.Data.SourcePos (noSourcePos)

import qualified Data.Text as Text

showFormula :: Formula -> String
showFormula f = showsPrecFormula 0 f ""

showsPrecFormula :: Int -> Formula -> ShowS
showsPrecFormula p = goShowFormula p 0

goShowFormula :: Int -> Int -> Formula -> ShowS
goShowFormula p d = dive
  where
    dive (All _ f) = showString "forall " . showBinder " " f
    dive (Exi _ f) = showString "exists " . showBinder " " f
    dive (Class _ f) = showString "{ " . showBinder " | " f . showString " }"
    dive (FinClass fs) = showString "{ " . flip (foldr ($)) (map (goShowFormula p d) fs) . showString " }"
    dive (InClass _ _ f) = showString "{ " . showBinder " | " f . showString " }"
    dive (Iff f g) = showParen True $ showInfix " iff "     f g
    dive (Imp f g) = showParen True $ showInfix " implies " f g
    dive (Or  f g) = showParen True $ showInfix " or "      f g
    dive (And f g) = showParen True $ showInfix " and "     f g
    dive (Tag a f) = showParen True $ shows a . showString " :: " . dive f
    dive (Not f)   = showString "not " . dive f
    dive Top       = showString "truth"
    dive Bot       = showString "contradiction"
    dive ThisT     = showString "ThisT"

    dive Trm{trmName = TermThesis} = showString "thesis"
    dive Trm{trmName = TermEquality, trmArgs = [l,r]} = showInfix " = " l r
    dive Trm{trmName = TermSymbolic tName, trmArgs = tArgs} = showString $ concat $
      zipWith (++) (Text.unpack <$> tName) (map (\t -> showParen (ambig t) (goShowFormula p d t) "") tArgs ++ [""])
    dive Trm{trmName = TermThe tName, trmArgs = tArgs} =
          showString ("the" <> Text.unpack tName) . showArguments tArgs
    dive Trm{trmName = tName, trmArgs = tArgs} = showString (Text.unpack $ termToText tName) . showArguments tArgs
    dive Var{varName = vName} = showString $ show vName
    dive Ind {indIndex = i }
      | i < d = showChar 'v' . shows (d - i - 1)
      | otherwise = showChar 'v' . showChar '?' . showString (show i)

    ambig Trm {trmName = TermSymbolic tName}
      | tName == [] = True
      | head tName == "" = tName /= ["", "lb", "rb"]
      | last tName == "" = True
    ambig _ = False

    showArguments _ | p == 1 = showString "(...)"
    showArguments ts =
      let showTerm = goShowFormula (pred p) d
      in  showArgumentsWith showTerm ts

    showBinder sep f = goShowFormula p (succ d) (Ind 0 noSourcePos) . showString sep .
      goShowFormula p (succ d) f

    showInfix operator f g = dive f . showString operator . dive g


showArgumentsWith :: (a -> ShowS) -> [a] -> ShowS
showArgumentsWith _ [] = id
showArgumentsWith showTerm ls = showParen True $ commaSeparated showTerm ls

commaSeparated :: (a -> ShowS) -> [a] -> ShowS
commaSeparated showTerm [] = id
commaSeparated showTerm [t] = showTerm t
commaSeparated showTerm (t:ts) = showTerm t . showChar ',' . commaSeparated showTerm ts
