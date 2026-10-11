-- |
-- Module      : SAD.Data.Terms
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
--
-- TODO: Add description.


{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Terms where

import Debug.Trace
import Data.Text (Text)
import Data.Text qualified as Text

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
  | TermEmpty
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
  represent (TermName t) = t
  represent (TermSymbolic t) = "s" <> t
  represent (TermNotion t) = "a" <> t
  represent (TermThe t) = "the" <> t
  represent (TermUnaryAdjective t) = "is" <> t
  represent (TermMultiAdjective t) = "mis" <> t
  represent (TermUnaryVerb t) = "do" <> t
  represent (TermMultiVerb t) = "mdo" <> t
  represent (TermTask n) = "tsk " <> Text.pack (show n)
  represent TermEquality = "="
  represent TermLess  = "iLess"
  represent TermThesis = "#TH#"
  represent TermEmpty = ""

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
