module SAD.Data.Formula.Show (
  showArgumentsWith,
  showTailWith,
  symEncode,
  symChars
  -- also exports show instance for Formula
  )where

import SAD.Data.Formula.Base
import SAD.Data.Formula.Kit


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

    dive t@Trm{trName = tName, trArgs = tArgs}
      | isThesis t = showString "thesis"
      | isEquality t = let [l,r] = trArgs t in showInfix " = " l r
      | isSymbolicTerm t = decode (tail tName) tArgs p d
      | not (null tName) && head tName == 't' =
          showString (tail tName) . showArguments tArgs
      | otherwise = showString tName . showArguments tArgs
    dive v@Var{trName = vName}
      | isUserVariable v = showString $ tail vName
      | otherwise = showString vName
    dive Ind {trIndx = i }
      | i < d = showChar 'v' . shows (d - i - 1)
      | otherwise = showChar 'v' . showChar '?' . showString (show i)

    showArguments _ | p == 1 = showString "(...)"
    showArguments ts =
      let showTerm = showFormula (pred p) d
      in  showArgumentsWith showTerm ts

    showBinder f = showFormula p (succ d) (Ind 0 undefined) . showChar ' ' .
      showFormula p (succ d) f

    showInfix operator f g = dive f . showString operator . dive g


showArgumentsWith :: (a -> ShowS) -> [a] -> ShowS
showArgumentsWith showTerm (t:ts) =
  showParen True $ showTerm t . showTailWith showTerm ts
showArgumentsWith _ _ = id

showTailWith :: (a -> ShowS) -> [a] -> ShowS
showTailWith showTerm = foldr ((.) . ((showChar ',' .) . showTerm)) id

isSymbolicTerm, isUserVariable :: Formula -> Bool
isSymbolicTerm Trm {trName = 's':_} = True; isSymbolicTerm _ = False
isUserVariable Var {trName = 'x':_} = True; isUserVariable _ = False

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


    ambig Trm {trName = 's':'d':'t':cs} = not $ funpatt cs
    ambig Trm {trName = t} = 
      head t == 's' && snd (splitAt (length t - 2) t) == "dt"
    ambig _ = False

    funpatt "lbdtrb" = True
    funpatt _ = False



-- Symbolic names

symChars :: [Char]
symChars = "`~!@$%^&*()-+=[]{}:'\"<>/?\\|;,"

symEncode :: String -> String
symEncode = concatMap chc
  where
    chc '`' = "bq" ; chc '~'  = "tl" ; chc '!' = "ex"
    chc '@' = "at" ; chc '$'  = "dl" ; chc '%' = "pc"
    chc '^' = "cf" ; chc '&'  = "et" ; chc '*' = "as"
    chc '(' = "lp" ; chc ')'  = "rp" ; chc '-' = "mn"
    chc '+' = "pl" ; chc '='  = "eq" ; chc '[' = "lb"
    chc ']' = "rb" ; chc '{'  = "lc" ; chc '}' = "rc"
    chc ':' = "cl" ; chc '\'' = "qt" ; chc '"' = "dq"
    chc '<' = "ls" ; chc '>'  = "gt" ; chc '/' = "sl"
    chc '?' = "qu" ; chc '\\' = "bs" ; chc '|' = "br"
    chc ';' = "sc" ; chc ','  = "cm" ; chc '.' = "dt"
    chc c   = ['z', c]

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