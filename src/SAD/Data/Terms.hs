{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module SAD.Data.Terms where

import Debug.Trace
import Data.Text (Text)
import qualified Data.Text as Text
import SAD.Core.Pretty
import Data.Set (Set)
import qualified Data.Set as Set
import SAD.Data.VarName
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import Data.Binary (Binary)

data TermName 
  = TermName Text
  | TermSymbolic Text
  | TermNotion Text
  | TermThe Text
  | TermUnaryAdjective Text
  | TermMultiAdjective Text
  | TermUnaryVerb Text
  | TermMultiVerb Text
  | TermTask Int
  | TermEquality
  | TermLess
  | TermThesis
  | TermEmpty
  | TermVar VarName
  deriving (Eq, Ord, Show, Read, Generic)
instance Hashable TermName
instance Binary TermName

newName :: TermName -> Maybe (Set TermName) -> TermName
newName n Nothing = n
newName n (Just taken) =
  let (c, n') = case n of
        (TermName t) -> (TermName, t)
        (TermSymbolic t) -> (TermSymbolic, t)
        (TermNotion t) -> (TermNotion, t)
        _ -> error "Not implemented"
  in head $ filter (`Set.notMember` taken) $ map (\x -> c $ n' <> Text.pack (show x)) [2::Int ..]

termFunction :: TermName
termFunction = TermNotion "Function"

termApplication :: TermName
termApplication = TermSymbolic "sdlbdtrb"

termDomain :: TermName
termDomain = TermSymbolic "zDzozmlpdtrp"

termSet :: TermName
termSet = TermNotion "Set"

termElement :: TermName
termElement = TermNotion "ElementOf"

termProduct :: TermName
termProduct = TermSymbolic "zPzrzozdlpdtcmdtrp"

termPair :: TermName
termPair = TermSymbolic "lpdtcmdtrp"

termObject :: TermName
termObject = TermNotion "Obj"

termSplit :: TermName -> (Text -> TermName, Text)
termSplit (TermNotion t) = (TermNotion, t)
termSplit (TermThe t) = (TermThe, t)
termSplit (TermUnaryAdjective t) = (TermUnaryAdjective, t)
termSplit (TermMultiAdjective t) = (TermMultiAdjective, t)
termSplit (TermUnaryVerb t) = (TermUnaryVerb, t)
termSplit (TermMultiVerb t) = (TermMultiVerb, t)
termSplit _ = error "wont happen"

instance Pretty TermName where
  pretty (TermName t) =  t
  pretty (TermSymbolic t) = decode t (repeat ".")
  pretty (TermNotion t) = "a" <>  t
  pretty (TermThe t) = "the" <>  t
  pretty (TermUnaryAdjective t) = "is" <>  t
  pretty (TermMultiAdjective t) = "mis" <>  t
  pretty (TermUnaryVerb t) = "do" <>  t
  pretty (TermMultiVerb t) = "mdo" <>  t
  pretty (TermTask n) = "tsk " <> Text.pack (show n)
  pretty TermEquality = "="
  pretty TermLess  = "iLess"
  pretty TermThesis = "#TH#"
  pretty TermEmpty = ""
  pretty (TermVar v) = pretty v

-- | Decode a TermSymbolic s with arguments ts
decode :: Text -> [Text] -> Text
decode s []     = symDecode s
decode s (t:ts) = Text.pack $ dec (Text.unpack s) ""
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
    dec ('d':'t':cs) = showString (Text.unpack (t <> decode (Text.pack cs) ts))
    dec ('z':c:cs@('d':'t':_)) = showChar c . showChar ' ' . dec cs
    dec ('z':c:cs)   = showChar c . dec cs
    dec cs@(':':_)   = showString cs
    dec []           = showString ""
    dec _            = showString (Text.unpack s)

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

symDecode :: Text -> Text
symDecode s = Text.pack $ sname [] (Text.unpack s)
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
    sname _ _             = Text.unpack s

data TermId
  = EqualityId
  | LessId
  | ThesisId
  | FunctionId
  | ApplicationId
  | DomainId
  | SetId
  | ElementId
  | ProductId
  | PairId
  | ObjectId
  | NewId -- ^ temporary id given to newly introduced symbols
  | SkolemId Int
  | SpecialId Int
  deriving (Eq, Ord, Show)

specialId :: Int -> TermId
specialId n =
  let msg =  "TermId: If you see this message, please file an issue."
  in case n of
  ( -1) -> trace msg $ EqualityId
  ( -2) -> trace msg $ LessId
  ( -3) -> trace msg $ ThesisId
  ( -4) -> trace msg $ FunctionId
  ( -5) -> trace msg $ ApplicationId
  ( -6) -> trace msg $ DomainId
  ( -7) -> trace msg $ SetId
  ( -8) -> trace msg $ ElementId
  ( -9) -> trace msg $ ProductId
  (-10) -> trace msg $ PairId
  (-11) -> trace msg $ ObjectId
  (-15) -> trace msg $ NewId
  n -> SpecialId n