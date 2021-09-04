{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Terms where

import Data.Text (Text)
import qualified Data.Text as Text
import SAD.Data.Identifier
import Data.Char

data TermName
  = TermName Text
  | TermSymbolic [Text]
  | TermNotion Text
  | TermThe Text
  | TermUnaryAdjective Text
  | TermMultiAdjective Text
  | TermUnaryVerb Text
  | TermMultiVerb Text
  | TermTask Int
  | TermEquality
  | TermThesis
  | TermEmpty
  deriving (Eq, Ord, Show)

termSet, termClass, termElement, termObject :: TermName
termSet = TermNotion "Set"
termClass = TermNotion "Class"
termElement = TermNotion "ElementOf"
termObject = TermNotion "Object"

termToIdent :: TermName -> Maybe Identifier
termToIdent (TermName t) = Just $ NormalIdent $ t
termToIdent (TermSymbolic ds) = Just $ SymbolIdent ds
termToIdent (TermNotion t) = Just $ NormalIdent $ case Text.uncons t of
  Nothing -> t
  Just (x, xs) -> Text.cons (toLower x) xs
termToIdent (TermThe t) = Just $ NormalIdent $ "the" <>  t
termToIdent (TermUnaryAdjective t) = Just $ NormalIdent $ "is" <>  t
termToIdent (TermMultiAdjective t) = Just $ NormalIdent $ "is" <>  t
termToIdent (TermUnaryVerb t) = Just $ NormalIdent $ "do" <>  t
termToIdent (TermMultiVerb t) = Just $ NormalIdent $ "do" <>  t
termToIdent _ = Nothing

termToText :: TermName -> Text
termToText (TermName t) = t
termToText (TermSymbolic ds) =
    Text.concat $ zipWith (<>) ds (replicate (length ds - 1) "." ++ [""])
termToText (TermNotion t) = "a" <>  t
termToText (TermThe t) = "the" <>  t
termToText (TermUnaryAdjective t) = "is" <>  t
termToText (TermMultiAdjective t) = "mis" <>  t
termToText (TermUnaryVerb t) = "do" <>  t
termToText (TermMultiVerb t) = "mdo" <>  t
termToText (TermTask n) = "tsk " <> Text.pack (show n)
termToText TermEquality = "="
termToText TermThesis = "#TH#"
termToText TermEmpty = ""

termSplit :: TermName -> (Text -> TermName, Text)
termSplit (TermNotion t) = (TermNotion, t)
termSplit (TermThe t) = (TermThe, t)
termSplit (TermUnaryAdjective t) = (TermUnaryAdjective, t)
termSplit (TermMultiAdjective t) = (TermMultiAdjective, t)
termSplit (TermUnaryVerb t) = (TermUnaryVerb, t)
termSplit (TermMultiVerb t) = (TermMultiVerb, t)
termSplit _ = error "wont happen"