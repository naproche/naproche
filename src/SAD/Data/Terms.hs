{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module SAD.Data.Terms where

import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import Data.Set (Set)
import qualified Data.Set as Set
import SAD.Data.VarName
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import Data.Binary (Binary)
import Control.DeepSeq (NFData)
import Data.Char

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
  | TermThesis
  | TermNotKnown
  | TermEmpty
  | TermVar VarName
  deriving (Eq, Ord, Show, Read, Generic)
instance NFData TermName
instance Hashable TermName
instance Binary TermName

newName :: TermName -> Maybe (Set TermName) -> TermName
newName n Nothing = n
newName n (Just taken) =
  let (c, n') = case n of
        (TermName t) -> (TermName, t)
        (TermSymbolic t) -> (TermSymbolic, t)
        (TermNotion t) -> (TermNotion, t)
        (TermThe t) -> (TermThe, t)
        x -> error $ "Not implemented: New name for " ++ show x
  in head $ filter (`Set.notMember` taken) $ map (\x -> c $ n' <> Text.pack (show x)) [2::Int ..]

termSet :: TermName
termSet = TermNotion "Set"

termClass :: TermName
termClass = TermNotion "Class"

termElement :: TermName
termElement = TermNotion "ElementOf"

termObject :: TermName
termObject = TermNotion "Object"

termSplit :: TermName -> (Text -> TermName, Text)
termSplit (TermNotion t) = (TermNotion, t)
termSplit (TermThe t) = (TermThe, t)
termSplit (TermUnaryAdjective t) = (TermUnaryAdjective, t)
termSplit (TermMultiAdjective t) = (TermMultiAdjective, t)
termSplit (TermUnaryVerb t) = (TermUnaryVerb, t)
termSplit (TermMultiVerb t) = (TermMultiVerb, t)
termSplit _ = error "wont happen"


termToText :: TermName -> Text
termToText (TermName t) = t
termToText (TermSymbolic t) =
    let ds = decode t
    in Text.concat $ zipWith (<>) ds (replicate (length ds - 1) "." ++ [""])
termToText (TermNotion t) = "a" <>  t
termToText (TermThe t) = "the" <>  t
termToText (TermUnaryAdjective t) = "is" <>  t
termToText (TermMultiAdjective t) = "mis" <>  t
termToText (TermUnaryVerb t) = "do" <>  t
termToText (TermMultiVerb t) = "mdo" <>  t
termToText (TermTask n) = "tsk " <> Text.pack (show n)
termToText TermEquality = "="
termToText TermThesis = "#TH#"
termToText TermNotKnown = "[??]"
termToText TermEmpty = ""
termToText (TermVar v) = let vp = varToText v
    in case Text.uncons vp of
      Nothing -> vp
      Just (h, t) -> Text.cons (toLower h) t

instance Pretty TermName where
  pretty t = pretty $ termToText t

-- | Decode a TermSymbolic s and return a list of fragments.
-- You can render the symbol 's' with arguments 'args' as
-- Text.concat $ zipWith (<>) (decode s) (args ++ [""])
decode :: Text -> [Text]
decode s = Text.split (=='.') $ symDecode s

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
  | ThesisId
  | ObjectId
  | SetId
  | ClassId
  | ElementId
  | NewId -- ^ temporary id given to newly introduced symbols
  | SkolemId Int
  | SpecialId Int
  deriving (Eq, Ord, Show)