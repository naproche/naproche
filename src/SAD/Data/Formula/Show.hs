-- |
-- Module      : SAD.Data.Formula.Show
-- Copyright   : (c) 2001 - 2008, Andrei Paskevich,
--               (c) 2017 - 2018, Steffen Frerix
--               (c) 2024, Marcel Schütz
-- License     : GPL-3
--
-- Show instance for formulas.


{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Formula.Show (
  symEncode
) where

import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as Text
import Data.List qualified as List

import SAD.Data.Formula.Base
import SAD.Data.Formula.Kit
import SAD.Data.VarName
import SAD.Data.Terms
import SAD.Export.Representation (toLazyText, represent)

import Isabelle.Position qualified as Position
import SAD.Helpers


instance Show Formula where
  showsPrec :: Int -> Formula -> ShowS
  showsPrec p = showsFormula p 0

showsFormula :: Int -> Int -> Formula -> ShowS
showsFormula p d f s = showFormula p d f ++ s

-- | Show a formula (depending of the current nesting depth of quantifiers).
showFormula :: Int -> Int -> Formula -> String
showFormula p = dive
  where
    -- Quantifier chain:
    dive d (All _ f@(All _ _)) = "\\<forall>" ++ showBindingVar p d ++ dive (d + 1) f
    dive d (All _ f@(Exi _ _)) = "\\<forall>" ++ showBindingVar p d ++ dive (d + 1) f
    dive d (All _ f@(Not (Exi _ _))) = "\\<forall>" ++ showBindingVar p d ++ dive (d + 1) f
    dive d (Exi _ f@(All _ _)) = "\\<exists>" ++ showBindingVar p d ++ dive (d + 1) f
    dive d (Exi _ f@(Exi _ _)) = "\\<exists>" ++ showBindingVar p d ++ dive (d + 1) f
    dive d (Exi _ f@(Not (Exi _ _))) = "\\<exists>" ++ showBindingVar p d ++ dive (d + 1) f
    dive d (Not (Exi _ f@(All _ _))) = "\\<nexists>" ++ showBindingVar p d ++ dive (d + 1) f
    dive d (Not (Exi _ f@(Exi _ _))) = "\\<nexists>" ++ showBindingVar p d ++ dive (d + 1) f
    dive d (Not (Exi _ f@(Not (Exi _ _)))) = "\\<nexists>" ++ showBindingVar p d ++ dive (d + 1) f
    -- Single quantifier:
    dive d (All _ f) = "\\<forall>" ++ showBindingVar p d ++ parens (dive (d + 1) f)
    dive d (Exi _ f) = "\\<exists>" ++ showBindingVar p d ++ parens (dive (d + 1) f)
    -- Negated existential quantifier:
    dive d (Not (Exi _ f)) = "\\<nexists>" ++ showBindingVar p d ++ parens (dive (d + 1) f)
    -- Equivalence:
    dive d (Iff f g) = showFormulaL p d f ++ " \\<Longleftrightarrow> " ++ showFormulaR p d g
    -- Implication:
    dive d (Imp f g) = showFormulaL p d f ++ " \\<Longrightarrow> " ++ showFormulaR p d g
    -- Disjunction chain:
    dive d (Or f@(Or _ _) g) = dive d f ++ " \\<or> " ++ showFormulaR p d g
    dive d (Or f g@(Or _ _)) = showFormulaL p d f ++ " \\<or> " ++ dive d g
    -- Disjunction:
    dive d (Or  f g) = showFormulaL p d f ++ " \\<or> " ++ showFormulaR p d g
    -- Conjunction chain:
    dive d (And f@(And _ _) g) = dive d f ++ " \\<and> " ++ showFormulaR p d g
    dive d (And f g@(And _ _)) = showFormulaL p d f ++ " \\<and> " ++ dive d g
    -- Conjunction:
    dive d (And f g) = showFormulaL p d f ++ " \\<and> " ++ showFormulaR p d g
    -- Tagged formula:
    dive d (Tag a f) = show a ++ " \\<Colon> " ++ showFormulaR p d f
    -- Inequality:
    dive d (Not Trm{trmName = TermEquality, trmArgs = [l, r]}) = dive d l ++ " \\<noteq> " ++ dive d r
    -- Negation:
    dive d (Not f) = "\\<not>" ++ showFormulaR p d f
    -- Truth:
    dive d Top = "\\<top>"
    -- Falsity:
    dive d Bot = "\\<bottom>"
    -- @ThisT@:
    dive d ThisT = "ThisT"
    -- Thesis:
    dive d Trm{trmName = TermThesis} = "thesis"
    -- Equality:
    dive d Trm{trmName = TermEquality, trmArgs = [l, r]} = dive d l ++ " = " ++ dive d r
    -- Symbolic formula/term:
    dive d Trm{trmName = TermSymbolic tName, trmArgs = tArgs} = decode (Text.unpack tName) tArgs p d ""
    -- Non-symbolic formula/term:
    dive d Trm{trmName = tName, trmArgs = tArgs} = Text.unpack (toLazyText (represent tName)) ++ showArguments p d tArgs
    -- Free variables:
    dive d Var{varName = VarConstant s} = Text.unpack s
    dive d Var{varName = vName} = Text.unpack $ toLazyText $ represent vName
    -- De Brujin index:
    dive d Ind{indIndex = i}
      | i < d = "v" ++ show (d - i - 1)
      | otherwise = "v?" ++ show i

-- | Show a formula that occurs on the left-hand side of a logical connective.
showFormulaL :: Int -> Int -> Formula -> String
showFormulaL p d f = parensIf (isAll f || isExi f || isIff f || isImp f || isOr f || isAnd f || isTag f) (showFormula p d f)

-- | Show a formula that occurs on the right-hand side of a logical connective.
showFormulaR :: Int -> Int -> Formula -> String
showFormulaR p d f = parensIf (isIff f || isImp f || isOr f || isAnd f || isTag f) (showFormula p d f)

-- | Show the arguments of a formula/term.
showArguments :: Int -> Int -> [Formula] -> String
showArguments _ _ [] = ""
showArguments p d terms =
  let showTerm = showFormula p d
  in "(" ++ List.intercalate "," (map showTerm terms) ++ ")"

-- | Show a binding variable.
showBindingVar :: Int -> Int -> String
showBindingVar p d = showFormula p (d + 1) (Ind 0 Position.none)

-- | Substitute all @.@ characters in a string by given terms.
substitute :: String -> [Formula] -> Int -> Int -> String
substitute s [] _ _ = s
substitute s (t : ts) p d = dec s
  where
    dec ('.' : cs) = parensIf (ambig t) (showFormula p d t) ++ substitute cs ts p d
    dec (c : cs@('.' : _)) | isAsciiLetter c = c : " " ++ dec cs
    dec (c : cs) = c : dec cs
    dec [] = ""

    ambig Trm {trmName = TermSymbolic tName} =
      ("." `Text.isPrefixOf` tName && Text.drop 2 tName /= "(.)") ||
      "." `Text.isSuffixOf` tName
    ambig _ = False



decode :: String -> [Formula] -> Int -> Int -> ShowS
decode s [] _ _ = showString (symDecode s)
decode s (t:ts) p d = dec s
  where
    dec ('b':'q':cs) = showChar '`' . dec cs
    dec ('t':'l':cs) = showChar '~' . dec cs
    dec ('e':'x':cs) = showChar '!' . dec cs
    dec ('a':'t':cs) = showChar '@' . dec cs
    dec ('d':'l':cs) = showChar '$' . dec cs
    dec ('p':'c':cs) = showChar '%' . dec cs
    dec ('c':'f':cs) = showChar '^' . dec cs
    dec ('e':'t':cs) = showChar '&' . dec cs
    dec ('a':'s':cs) = showChar '*' . dec cs
    dec ('l':'p':cs) = showChar '(' . dec cs
    dec ('r':'p':cs) = showChar ')' . dec cs
    dec ('m':'n':cs) = showChar '-' . dec cs
    dec ('p':'l':cs) = showChar '+' . dec cs
    dec ('e':'q':cs) = showChar '=' . dec cs
    dec ('l':'b':cs) = showChar '[' . dec cs
    dec ('r':'b':cs) = showChar ']' . dec cs
    dec ('l':'c':cs) = showChar '{' . dec cs
    dec ('r':'c':cs) = showChar '}' . dec cs
    dec ('c':'l':cs) = showChar ':' . dec cs
    dec ('q':'t':cs) = showChar '\'' . dec cs
    dec ('d':'q':cs) = showChar '"' . dec cs
    dec ('l':'s':cs) = showChar '<' . dec cs
    dec ('g':'t':cs) = showChar '>' . dec cs
    dec ('s':'l':cs) = showChar '/' . dec cs
    dec ('q':'u':cs) = showChar '?' . dec cs
    dec ('b':'s':cs) = showChar '\\' . dec cs
    dec ('b':'r':cs) = showChar '|' . dec cs
    dec ('s':'c':cs) = showChar ';' . dec cs
    dec ('c':'m':cs) = showChar ',' . dec cs
    dec ('u':'s':cs) = showChar '_' . dec cs
    dec ('h':'s':cs) = showChar '#' . dec cs
    dec ('d':'t':cs) =
      showParen (ambig t) (showsFormula p d t) . decode cs ts p d
    dec ('z':c:cs@('d':'t':_)) = showChar c . showChar ' ' . dec cs
    dec ('z':c:cs)   = showChar c . dec cs
    dec cs@(':':_)   = showString cs
    dec []           = showString ""
    dec _            = showString s

    ambig Trm {trmName = TermSymbolic tName} | "dt" `Text.isPrefixOf` tName = not $ appPattern (Text.drop 3 tName)
    ambig Trm {trmName = TermSymbolic tName} =
      snd (Text.splitAt (Text.length tName - 2) tName) == "dt"
    ambig _ = False

    -- map application: "(.)"
    appPattern "lpdtrp" = True
    appPattern _ = False
-- Symbolic names

symEncode :: Text -> Text
symEncode = Text.concat . map chc . Text.chunksOf 1
  where
    chc :: Text -> Text
    chc "`" = "bq" ; chc "~"  = "tl" ; chc "!" = "ex"
    chc "@" = "at" ; chc "$"  = "dl" ; chc "%" = "pc"
    chc "^" = "cf" ; chc "&"  = "et" ; chc "*" = "as"
    chc "(" = "lp" ; chc ")"  = "rp" ; chc "-" = "mn"
    chc "+" = "pl" ; chc "="  = "eq" ; chc "[" = "lb"
    chc "]" = "rb" ; chc "{"  = "lc" ; chc "}" = "rc"
    chc ":" = "cl" ; chc "\'" = "qt" ; chc "\"" = "dq"
    chc "<" = "ls" ; chc ">"  = "gt" ; chc "/" = "sl"
    chc "?" = "qu" ; chc "\\" = "bs" ; chc "|" = "br"
    chc ";" = "sc" ; chc ","  = "cm" ; chc "." = "dt"
    chc "_" = "us" ; chc "#"  = "hs"
    chc c   = Text.cons 'z' c

symDecode :: String -> String
symDecode s = sname [] s
  where
    sname ac ('b':'q':cs) = sname ('`':ac) cs
    sname ac ('t':'l':cs) = sname ('~':ac) cs
    sname ac ('e':'x':cs) = sname ('!':ac) cs
    sname ac ('a':'t':cs) = sname ('@':ac) cs
    sname ac ('d':'l':cs) = sname ('$':ac) cs
    sname ac ('p':'c':cs) = sname ('%':ac) cs
    sname ac ('c':'f':cs) = sname ('^':ac) cs
    sname ac ('e':'t':cs) = sname ('&':ac) cs
    sname ac ('a':'s':cs) = sname ('*':ac) cs
    sname ac ('l':'p':cs) = sname ('(':ac) cs
    sname ac ('r':'p':cs) = sname (')':ac) cs
    sname ac ('m':'n':cs) = sname ('-':ac) cs
    sname ac ('p':'l':cs) = sname ('+':ac) cs
    sname ac ('e':'q':cs) = sname ('=':ac) cs
    sname ac ('l':'b':cs) = sname ('[':ac) cs
    sname ac ('r':'b':cs) = sname (']':ac) cs
    sname ac ('l':'c':cs) = sname ('{':ac) cs
    sname ac ('r':'c':cs) = sname ('}':ac) cs
    sname ac ('c':'l':cs) = sname (':':ac) cs
    sname ac ('q':'t':cs) = sname ('\'':ac) cs
    sname ac ('d':'q':cs) = sname ('"':ac) cs
    sname ac ('l':'s':cs) = sname ('<':ac) cs
    sname ac ('g':'t':cs) = sname ('>':ac) cs
    sname ac ('s':'l':cs) = sname ('/':ac) cs
    sname ac ('q':'u':cs) = sname ('?':ac) cs
    sname ac ('b':'s':cs) = sname ('\\':ac) cs
    sname ac ('b':'r':cs) = sname ('|':ac) cs
    sname ac ('s':'c':cs) = sname (';':ac) cs
    sname ac ('c':'m':cs) = sname (',':ac) cs
    sname ac ('d':'t':cs) = sname ('.':ac) cs
    sname ac ('u':'s':cs) = sname ('_':ac) cs
    sname ac ('h':'s':cs) = sname ('#':ac) cs
    sname ac ('z':c:cs)   = sname (c:ac) cs
    sname ac cs@(':':_)   = reverse ac ++ cs
    sname ac []           = reverse ac
    sname _ _             = s