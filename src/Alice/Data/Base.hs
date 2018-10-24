{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Basic data types and formula show instance.
-}


module Alice.Data.Base where

import qualified Data.IntMap.Strict as IM


-- Formulas

data Formula  = All String  Formula       | Exi String  Formula
              | Iff Formula Formula       | Imp Formula Formula
              | Or  Formula Formula       | And Formula Formula
              | Tag Tag Formula           | Not Formula
              | Top                       | Bot
              | Trm { trName :: String,
                      trArgs :: [Formula],  trInfo :: [Formula] , trId :: Int}
              | Var { trName :: String,     trInfo :: [Formula] }
              | Ind { trIndx :: Int }
              | ThisT


-- Tags

data Tag  = DIG | DMS | DMP | DHD | DIH | DCH | DEC
          -- Tags to mark certain parts of function definitions
          | DMK | DEV | DCD | DEF | DDM | DRP
          -- Tags to mark parts in function proof tasks
          | FDM | FEX | FUQ | FCH | FDC
          deriving (Eq, Show)


  -- DIH -> induction hypothesis
  -- DCH -> case hypothesis
  -- DHD -> Head of definition
  -- DEC -> signals computational reasoning
  -- DMK -> mark to prevent multiple unfolds of the same term during unfolding
  -- DIG is used in parsing
  -- DMS -"-
  -- DMP -"-

{- whether a Tag marks a part in a function proof task -}
fnTag :: Tag -> Bool
fnTag FDM = True; fnTag FCH = True; fnTag FEX = True; fnTag FUQ = True
fnTag _   = False


-- rewrite rules

data Rule = Rule {
  rlLeft :: Formula,   -- left side
  rlRght :: Formula,   -- right side
  rlCond :: [Formula], -- conditions
  rlLabl :: String }   -- label

instance Show Rule where
  show rl = 
    show (rlLeft rl) ++ " = " ++ show (rlRght rl) ++
    ", Cond: " ++ show (rlCond rl) ++ ", Label: " ++ show (rlLabl rl)

printrules :: [Rule] -> String
printrules = unlines . map show

-- definitions

data DefType = Signature | Definition deriving (Eq, Show)
data DefEntry = DE {
  dfGrds :: [Formula],   -- guards of the definitions
  dfForm :: Formula,     -- defining formula
  dfType :: DefType,     -- proper definition or only sig extension
  dfTerm :: Formula,     -- defined term
  dfEvid :: [Formula],   -- evidence from the defining formula
  dfTplk :: [[Formula]]  -- type-likes of the definition
  } deriving Show

{- yields information as to what can be unfolded -}
dfSign :: DefEntry -> Bool
dfSign df = dfSign' $ dfType df
  where
    dfSign' Definition = True
    dfSign' _ = False

{- storage of definitions by term id -}
type Definitions = IM.IntMap DefEntry


-- evaluations
data Eval = EV {
  evTerm :: Formula,  -- the term to be reduced
  evPos  :: Formula,  -- reduction for positive positions
  evNeg  :: Formula,  -- reduction for negative positions
  evCond :: [Formula] -- conditions
  } deriving Show


-- show instances

instance Show Formula where
  showsPrec p = showFormula p 0

showFormula :: Int -> Int -> Formula -> ShowS
showFormula p d = dive
    where
      dive (All s f)  = showString "forall " . binder f
      dive (Exi s f)  = showString "exists " . binder f
      dive (Iff f g)  = showParen True $ sinfix " iff " f g
      dive (Imp f g)  = showParen True $ sinfix " implies " f g
      dive (Or  f g)  = showParen True $ sinfix " or "  f g
      dive (And f g)  = showParen True $ sinfix " and " f g
      dive (Tag DMK f) = dive f
      dive (Tag a f)  = showParen True $ shows a
                      . showString " :: " . dive f
      dive (Not f)    = showString "not " . dive f
      dive Top        = showString "truth"
      dive Bot        = showString "contradiction"
      dive ThisT      = showString "ThisT"

      dive Trm {trName = "#TH#"}   = showString "thesis"
      dive Trm {trName = "=", trArgs = [l,r]}  = sinfix " = " l r
      dive Trm {trName = 's':s, trArgs = ts} = decode s ts p d
      dive Trm {trName = 't':s, trArgs = ts} = showString s . sargs ts
      dive Trm {trName = s, trArgs = ts}       = showString s . sargs ts
      dive Var {trName = 'x':s}      = showString s
      dive Var {trName = s}            = showString s
      dive (Ind i )    | i < d = showChar 'v' . shows (d - i - 1)
                        | True  = showChar 'v' . showChar '?' . showString (show i)

      sargs []  = id
      sargs _   | p == 1  = showString "(...)"
      sargs ts  = showArgs (showFormula (pred p) d) ts

      binder f      = showFormula p (succ d) (Ind 0) . showChar ' '
                    . showFormula p (succ d) f

      sinfix o f g  = dive f . showString o . dive g

showArgs sh (t:ts)  = showParen True $ sh t . showTail sh ts
showArgs _ _        = id

showTail sh ts      = foldr ((.) . ((showChar ',' .) . sh)) id ts

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
    ambig Trm {trName = t} = head t == 's' && snd (splitAt (length t - 2) t) == "dt"
    ambig _ = False

    funpatt "lbdtrb" = True
    funpatt _ = False



-- Symbolic names

symChars    = "`~!@$%^&*()-+=[]{}:'\"<>/?\\|;,"

symEncode s = concatMap chc s
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




ifM :: (Monad m) => m Bool -> m a -> m a -> m a
ifM p f g = do b <- p; if b then f else g
