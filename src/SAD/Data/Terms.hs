-- |
-- Module      : SAD.Data.Terms
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Terms where

import Debug.Trace
import Data.Text.Lazy (Text)
import Data.Text.Lazy.Builder (fromLazyText, fromString)

import SAD.Export.Representation
import SAD.Helpers (failureMessage)


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

instance Representation TermName where
  represent (TermName t) = fromLazyText t
  represent (TermSymbolic t) = "s" <> fromLazyText t
  represent (TermNotion t) = "a" <> fromLazyText t
  represent (TermThe t) = "the" <> fromLazyText t
  represent (TermUnaryAdjective t) = "is" <> fromLazyText t
  represent (TermMultiAdjective t) = "mis" <> fromLazyText t
  represent (TermUnaryVerb t) = "do" <> fromLazyText t
  represent (TermMultiVerb t) = "mdo" <> fromLazyText t
  represent (TermTask n) = "tsk " <> fromString (show n)
  represent TermEquality = "="
  represent TermLess  = "iLess"
  represent TermThesis = "#TH#"

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
specialId n =
  let msg = failureMessage "SAD.Data.Terms.TermId" "Invalid term ID."
  in case n of
  ( -1) -> trace msg EqualityId
  ( -2) -> trace msg LessId
  ( -3) -> trace msg ThesisId
  ( -4) -> trace msg FunctionId
  ( -5) -> trace msg ApplicationId
  ( -6) -> trace msg DomainId
  ( -7) -> trace msg SetId
  ( -8) -> trace msg ElementId
  ( -9) -> trace msg ClassId
  (-10) -> trace msg PairId
  (-11) -> trace msg ObjectId
  (-12) -> trace msg MapId
  (-15) -> trace msg NewId
  n -> SpecialId n
