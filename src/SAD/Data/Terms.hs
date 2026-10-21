-- |
-- Module      : SAD.Data.Terms
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Terms where

import Data.Text (Text)
import Data.Text qualified as Text

import SAD.Export.Presentation


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
  deriving (Eq, Ord, Show)

termFunction :: TermName
termFunction = TermNotion "Function"

termMap, termSet, termClass, termElement, termObject :: TermName
termMap = TermNotion "Map"
termSet = TermNotion "Set"
termClass = TermNotion "Class"
termObject = TermNotion "Object"
termElement = TermNotion "ElementOf"

termApplication, termDomain, termPair :: TermName
termApplication = TermName "dtlpdtrp" -- ".(.)"
termDomain = TermName "zDzozmlpdtrp"  -- "Dom(.)"
termPair = TermName "lpdtcmdtrp"      -- "(.,.)"

termSplit :: TermName -> (Text -> TermName, Text)
termSplit (TermNotion t) = (TermNotion, t)
termSplit (TermThe t) = (TermThe, t)
termSplit (TermUnaryAdjective t) = (TermUnaryAdjective, t)
termSplit (TermMultiAdjective t) = (TermMultiAdjective, t)
termSplit (TermUnaryVerb t) = (TermUnaryVerb, t)
termSplit (TermMultiVerb t) = (TermMultiVerb, t)
termSplit _ = undefined

instance Presentation TermName where
  present (TermName t) = t
  present (TermSymbolic t) = "s" <> t
  present (TermNotion t) = "a" <> t
  present (TermThe t) = "the" <> t
  present (TermUnaryAdjective t) = "is" <> t
  present (TermMultiAdjective t) = "mis" <> t
  present (TermUnaryVerb t) = "do" <> t
  present (TermMultiVerb t) = "mdo" <> t
  present (TermTask n) = "tsk " <> Text.pack (show n)
  present TermEquality = "="
  present TermLess = "iLess"
  present TermThesis = "#TH#"

data TermId
  = EqualityId
  | LessId
  | ThesisId
  | FunctionId
  | MapId
  | ApplicationId
  | DomainId
  | SetId
  | ClassId
  | ElementId
  | PairId
  | ObjectId
  | NewId -- ^ temporary id given to newly introduced symbols
  | SkolemId Int
  | SpecialId Int
  deriving (Eq, Ord, Show)

specialId :: Int -> TermId
specialId n = case n of
  ( -1) -> EqualityId
  ( -2) -> LessId
  ( -3) -> ThesisId
  ( -4) -> FunctionId
  ( -5) -> ApplicationId
  ( -6) -> DomainId
  ( -7) -> SetId
  ( -8) -> ElementId
  ( -9) -> ClassId
  (-10) -> PairId
  (-11) -> ObjectId
  (-12) -> MapId
  (-15) -> NewId
  n -> SpecialId n
