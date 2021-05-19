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

module SAD.Core.Identifier
  ( Ident(..)
  , isSymbol, isNormal, prettyWithArgs
  , newIdent, symChars, symEncode, symDecode
  , identAsType, identAsTerm, identAsVar
  , FV(..), FreeVarStrategy(..), fvFromVarSet, fvToVarSet, bindVarSet
  , identSet, identClass, identElement, identObject
  ) where

import Control.Monad
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

data Ident
  = NormalIdent { fromNormalIdent :: !Text } -- ^ An alpha-numeric identifier
  | SymbolIdent [Text] -- ^ parts of the symbol with space for an argument between each two list elements
  deriving (Eq, Ord, Show, Read, Generic)
instance NFData Ident
instance Hashable Ident
instance Binary Ident

identSet, identClass, identElement, identObject :: Ident
identSet = NormalIdent "set"
identClass = NormalIdent "class"
identElement = NormalIdent "elementOf"
identObject = NormalIdent "object"

isSymbol :: Ident -> Bool
isSymbol = \case SymbolIdent _ -> True; _ -> False

isNormal :: Ident -> Bool
isNormal = \case NormalIdent _ -> True; _ -> False

instance Pretty Ident where
  pretty (NormalIdent t) = pretty t
  pretty (SymbolIdent ts) = pretty $ Text.intercalate "." ts

alternate :: [a] -> [a] -> [a]
alternate [] _ = []
alternate (x:xs) (y:ys) = x : y : alternate xs ys
alternate (x:xs) [] = x : alternate xs []

prettyWithArgs :: Ident -> [Doc ann] -> Doc ann
prettyWithArgs (NormalIdent s) args = pretty s <> tupled args
prettyWithArgs (SymbolIdent s) args = concatWith (<+>) $ fmap (either pretty id)
  -- we filter out the empty string to avoid spaces
  $ filter (either (/="") (const True))
  $ alternate (map Left s) $ map Right args

-- | Pick a new identifier similar to the old
-- and not contained in 'taken'.
-- TODO: This is linear in the number of similar idents already taken
-- and can thus become quadratic when many idents are overloaded!
newIdent :: Ident -> Set Ident -> Ident
newIdent n taken =
  case n of
    NormalIdent n' ->
      head $ filter (`Set.notMember` taken) $ n : map (\x -> NormalIdent $ n' <> Text.pack (show x)) [2::Int ..]
    SymbolIdent ns ->
      head $ filter (`Set.notMember` taken) $ n : map (\x -> SymbolIdent $ onLast (<> Text.pack (show x)) ns) [2::Int ..]
  where
    onLast f xs = case xs of
      [] -> [f ""]
      [x] -> [f x]
      [x, ""] -> [f x, ""]
      [x, "", ""] -> [f x, "", ""]
      (x:xs) -> x : onLast f xs

identAsType :: Ident -> Maybe Text
identAsType (NormalIdent t) = Just t
identAsType (SymbolIdent _) = Nothing

identAsTerm :: Ident -> Text
identAsTerm (NormalIdent n) = "i" <> n
identAsTerm (SymbolIdent xs) = case extractTex xs of
  Just n -> "t" <> n
  Nothing -> "s" <> identAsTPTP xs

identAsVar :: Ident -> Text
identAsVar (NormalIdent n) = "I" <> n
identAsVar (SymbolIdent xs) = case extractTex xs of
  Just n -> "T" <> n
  Nothing -> "S" <> identAsTPTP xs

-- | Try to extract a tex command 'com' used as '\com{.}{.}' from a symbol.
extractTex :: [Text] -> Maybe Text
extractTex t = do
  (x, xs) <- List.uncons t
  ('\\', rest) <- Text.uncons x
  (command, '{') <- Text.unsnoc rest
  if all (\x -> x == "}{" || x == "}") xs
    then pure command
    else Nothing

identAsTPTP :: [Text] -> Text
identAsTPTP = Text.intercalate "__" . map symEncode

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
