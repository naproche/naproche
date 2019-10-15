{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Formula.Show (
  showArgumentsWith,
  commaSeparated,
  symEncode,
  symChars
  -- also exports show instance for Formula
  )where

import SAD.Data.Formula.Base
import SAD.Data.VarName
import SAD.Data.Terms
import SAD.Export.Representation (toLazyText, represent)
import SAD.Core.SourcePos (noSourcePos)

import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as Text

-- show instances

instance Show Formula where
  showsPrec p = showFormula p 0

showFormula :: Int -> Int -> Formula -> ShowS
showFormula p d = dive
  where
    dive (All _ f) = showString "forall " . showBinder f
    dive (Exi _ f) = showString "exists " . showBinder f
    dive (Iff f g) = showParen True $ showInfix " iff "     f g
    dive (Imp f g) = showParen True $ showInfix " implies " f g
    dive (Or  f g) = showParen True $ showInfix " or "      f g
    dive (And f g) = showParen True $ showInfix " and "     f g
    dive (Tag a f) = showParen True $ shows a . showString " :: " . dive f
    dive (Not f)   = showString "not " . dive f
    dive Top       = showString "truth"
    dive Bot       = showString "contradiction"
    dive ThisT     = showString "ThisT"

    dive t@Trm{trmName = TermThesis} = showString "thesis"
    dive t@Trm{trmName = TermEquality, trmArgs = [l,r]} = showInfix " = " l r
    dive t@Trm{trmName = TermSymbolic tName, trmArgs = tArgs} = decode (Text.unpack tName) tArgs p d
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
      let showTerm = showFormula (pred p) d
      in  showArgumentsWith showTerm ts

    showBinder f = showFormula p (succ d) (Ind 0 noSourcePos) . showChar ' ' .
      showFormula p (succ d) f

    showInfix operator f g = dive f . showString operator . dive g


showArgumentsWith :: (a -> ShowS) -> [a] -> ShowS
showArgumentsWith _ [] = id
showArgumentsWith showTerm ls = showParen True $ commaSeparated showTerm ls

commaSeparated :: (a -> ShowS) -> [a] -> ShowS
commaSeparated showTerm [] = id
commaSeparated showTerm [t] = showTerm t
commaSeparated showTerm (t:ts) = showTerm t . showChar ',' . commaSeparated showTerm ts

-- decoding of symbolic names

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
    dec ('d':'t':cs) =
      showParen (ambig t) (showFormula p d t) . decode cs ts p d
    dec ('z':c:cs@('d':'t':_)) = showChar c . showChar ' ' . dec cs
    dec ('z':c:cs)   = showChar c . dec cs
    dec cs@(':':_)   = showString cs
    dec []           = showString ""
    dec _            = showString s


    ambig Trm {trmName = TermSymbolic tName} | "dt" `Text.isPrefixOf` tName = not $ funPat (Text.drop 3 tName)
    ambig Trm {trmName = TermSymbolic tName} =
      snd (Text.splitAt (Text.length tName - 2) tName) == "dt"
    ambig _ = False

    funPat "lbdtrb" = True
    funPat _ = False



-- Symbolic names

symChars :: String
symChars = "`~!@$%^&*()-+=[]{}:'\"<>/?\\|;,"

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
    sname ac ('z':c:cs)   = sname (c:ac) cs
    sname ac cs@(':':_)   = reverse ac ++ cs
    sname ac []           = reverse ac
    sname _ _             = s
