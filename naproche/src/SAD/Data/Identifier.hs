{-# LANGUAGE OverloadedStrings #-}

-- | Identifiers are somewhat challenging: Naproche accepts both
-- alphanumber and symbolic identifiers which need to have a
-- non-overlapping representation in TPTP. Also, variables are
-- written with an upper-case first letter and constants with
-- a lower-case first letter in TPTP.

-- An identifier is an abstract representation that takes
-- Naproche identifiers and can be rendered injectively
-- into TPTP. It stores the representation given by the user
-- in its constructors and can be pretty-printed.

module SAD.Data.Identifier
  ( Ident(..), Identifier(..)
  , isSymbol, isNormal, prettyWithArgs
  , symChars, symEncode, symDecode
  , identifierAsType, identifierAsTerm, identifierAsVar
  , FV(..), FreeVarStrategy(..), fvFromVarSet, fvToVarSet, bindVarSet
  , identifierSet, identifierClass, identifierElement, identifierObject, identifierHole, identifierEmpty
  ) where

import Control.Monad ( zipWithM )
import qualified Data.List as List
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Magic (oneShot)
import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import Data.Binary (Binary)
import Control.DeepSeq (NFData)

-- | Unique identifiers. As an invariant, any Ident 'i' generated
-- from an Identifier 'id' has: 'sourceIdentifier i == id'.
data Ident = Ident
  { uniqueIdentifier :: Identifier
  , sourceIdentifier :: Identifier
  } deriving (Eq, Ord, Show, Read, Generic)
instance NFData Ident
instance Hashable Ident
instance Binary Ident

instance Pretty Ident where
  pretty (Ident u p) = pretty p

data Identifier
  = NormalIdent { fromNormalIdent :: !Text } -- ^ An alpha-numeric identifier
  | SymbolIdent [Text] -- ^ parts of the symbol with space for an argument between each two list elements
  deriving (Eq, Ord, Show, Read, Generic)
instance NFData Identifier
instance Hashable Identifier
instance Binary Identifier

-- | Built-in identifiers. The 'ident' variant is in Core.Unique
identifierSet, identifierClass, identifierElement, identifierObject :: Identifier
identifierSet = NormalIdent "set"
identifierClass = NormalIdent "class"
identifierElement = NormalIdent "elementOf"
identifierObject = NormalIdent "object"

-- | Illegal identifiers that are only to be used for prettier output.
identifierHole, identifierEmpty :: Identifier
identifierHole = NormalIdent "[??]"
identifierEmpty = NormalIdent ""

isSymbol :: Ident -> Bool
isSymbol (Ident u _) = isSymbol' u

isSymbol' :: Identifier -> Bool
isSymbol' = \case SymbolIdent _ -> True; _ -> False

isNormal :: Ident -> Bool
isNormal (Ident u _) = isNormal' u

isNormal' :: Identifier -> Bool
isNormal' = \case NormalIdent _ -> True; _ -> False

instance Pretty Identifier where
  pretty (NormalIdent t) = pretty t
  pretty (SymbolIdent ts) = pretty $ Text.intercalate "." ts

alternate :: [a] -> [a] -> [a]
alternate [] _ = []
alternate (x:xs) (y:ys) = x : y : alternate xs ys
alternate (x:xs) [] = x : alternate xs []

prettyWithArgs :: Ident -> [Doc ann] -> Doc ann
prettyWithArgs (Ident _ p) = prettyWithArgs' p

prettyWithArgs' :: Identifier -> [Doc ann] -> Doc ann
prettyWithArgs' (NormalIdent s) args = pretty s <> tupled args
prettyWithArgs' (SymbolIdent s) args = concatWith (<+>) $ fmap (either pretty id)
  -- we filter out the empty string to avoid spaces
  $ filter (either (/="") (const True))
  $ alternate (map Left s) $ map Right args

identifierAsType :: Identifier -> Maybe Text
identifierAsType (NormalIdent t) = Just t
identifierAsType (SymbolIdent _) = Nothing

identifierAsTerm :: Identifier -> Text
identifierAsTerm (NormalIdent n) = "i" <> n
identifierAsTerm (SymbolIdent xs) = case extractTex xs of
  Just n -> "t" <> n
  Nothing -> "s" <> identifierAsTPTP xs

identifierAsVar :: Identifier -> Text
identifierAsVar (NormalIdent n) = "I" <> n
identifierAsVar (SymbolIdent xs) = case extractTex xs of
  Just n -> "T" <> n
  Nothing -> "S" <> identifierAsTPTP xs

-- | Try to extract a tex command 'com' used as '\com{.}{.}' from a symbol.
extractTex :: [Text] -> Maybe Text
extractTex t = do
  (x, xs) <- List.uncons t
  ('\\', rest) <- Text.uncons x
  (command, '{') <- Text.unsnoc rest
  if all (\x -> x == "}{" || x == "}") xs
    then pure command
    else Nothing

identifierAsTPTP :: [Text] -> Text
identifierAsTPTP = Text.intercalate "__" . map symEncode

symChars :: String
symChars = "`~!@$%^&*()-+=[]{}:'\"<>/?\\|;,"

symEncode :: Text -> Text
symEncode = Text.concat . joinEithers . map chc . Text.chunksOf 1
  where
    chc :: Text -> Either Text Text
    chc "`" = Right "bq" ; chc "~"  = Right "tl" ; chc "!"  = Right "ex"
    chc "@" = Right "at" ; chc "$"  = Right "dl" ; chc "%"  = Right "pc"
    chc "^" = Right "cf" ; chc "&"  = Right "et" ; chc "*"  = Right "as"
    chc "(" = Right "lp" ; chc ")"  = Right "rp" ; chc "-"  = Right "mn"
    chc "+" = Right "pl" ; chc "="  = Right "eq" ; chc "["  = Right "lb"
    chc "]" = Right "rb" ; chc "{"  = Right "lc" ; chc "}"  = Right "rc"
    chc ":" = Right "cl" ; chc "\'" = Right "qt" ; chc "\"" = Right "dq"
    chc "<" = Right "ls" ; chc ">"  = Right "gt" ; chc "/"  = Right "sl"
    chc "?" = Right "qu" ; chc "\\" = Right "bs" ; chc "|"  = Right "br"
    chc ";" = Right "sc" ; chc ","  = Right "cm" ; chc "_"  = Right "us"
    chc c   = Left c

    joinEithers [] = []
    joinEithers xs@(Right _ : _) = "_" : go xs
    joinEithers xs@(Left _ : _) = go xs

    go [] = []
    go [Right x] = [x]
    go [Left x] = [x]
    go (x:y:xs) = case (x, y) of
      (Right x', Right _) -> x'       : go (y:xs)
      (Right x', Left  _) -> x' : "_" : go (y:xs)
      (Left  x', Right _) -> x' : "_" : go (y:xs)
      (Left  x', Left  _) -> x'       : go (y:xs)

-- | The decoder for/inverse of symEncode.
-- symDecode . symEncode = Just
-- (fmap symEncode . symDecode)(t) \in {Nothing, Just t}
symDecode :: Text -> Maybe Text
symDecode t = case Text.uncons t of
  Nothing -> Just ""
  Just ('_', t) -> Text.concat <$> zipWithM ($) (tail fns) (Text.split (=='_') t)
  Just _ -> Text.concat <$> zipWithM ($) fns (Text.split (=='_') t)
  where
    fns = concat $ repeat [decodeLeft, decodeRight]
    decodeLeft = Just
    decodeRight = fmap Text.concat . mapM chc . Text.chunksOf 2
    chc "bq" = Just "`" ; chc "tl" = Just "~"  ; chc "ex" = Just "!"
    chc "at" = Just "@" ; chc "dl" = Just "$"  ; chc "pc" = Just "%"
    chc "cf" = Just "^" ; chc "el" = Just "&"  ; chc "as" = Just "*"
    chc "lp" = Just "(" ; chc "rp" = Just ")"  ; chc "mn" = Just "-"
    chc "pl" = Just "+" ; chc "eq" = Just "="  ; chc "lb" = Just "["
    chc "rb" = Just "]" ; chc "lc" = Just "{"  ; chc "rc" = Just "}"
    chc "cl" = Just ":" ; chc "qt" = Just "\'" ; chc "dq" = Just "\""
    chc "ls" = Just "<" ; chc "gt" = Just ">"  ; chc "sl" = Just "/"
    chc "qu" = Just "?" ; chc "bs" = Just "\\" ; chc "br" = Just "|"
    chc "sc" = Just ";" ; chc "cm" = Just ","  ; chc "us" = Just "_"
    chc _ = Nothing

--- Free variable traversals, see
--- https://www.haskell.org/ghc/blog/20190728-free-variable-traversals.html

newtype FV = FV { runFV :: Set Ident   -- bound variable set
                        -> Set Ident   -- the accumulator
                        -> Set Ident   -- the result
                }

instance Monoid FV where
  mempty = FV $ \_ acc -> acc

instance Semigroup FV where
  fv1 <> fv2 = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
    runFV fv1 boundVars (runFV fv2 boundVars acc)

class Monoid a => FreeVarStrategy a where
  unitFV :: Ident -> a
  bindVar :: Ident -> a -> a

instance FreeVarStrategy FV where
  unitFV v = FV $ \boundVars acc ->
    if v `Set.member` boundVars
    then acc
    else Set.insert v acc
  bindVar v fv = FV $ \boundVars acc ->
    runFV fv (Set.insert v boundVars) acc

fvFromVarSet :: Set Ident -> FV
fvFromVarSet vs = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  acc `Set.union` Set.filter (`Set.notMember` boundVars) vs

fvToVarSet :: FV -> Set Ident
fvToVarSet fv = runFV fv mempty mempty

excludeVars :: FV -> FV -> FV
excludeVars fv1 fv2 = FV $ oneShot $ \boundVars -> oneShot $ \acc ->
  runFV fv2 (runFV fv1 mempty boundVars) acc

bindVarSet :: Set Ident -> FV -> FV
bindVarSet vs = excludeVars (fvFromVarSet vs)
