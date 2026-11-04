{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.Terms
-- Description : TODO
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
module SAD.Data.Terms where

import Isabelle.Library (show_text)

import SAD.Data.Pattern
import SAD.Export.Presentation


-- * Term Names

data TermName
  = TermSymbolic Pattern
  | TermNotion Pattern
  | TermThe Pattern
  | TermUnaryAdjective Pattern
  | TermMultiAdjective Pattern
  | TermUnaryVerb Pattern
  | TermMultiVerb Pattern
  | TermTask Int
  | TermEquality
  | TermLess
  | TermThesis
  deriving (Eq, Ord, Show)

termFunction, termMap, termSet, termClass, termElement, termObject,
  termApplication, termDomain, termPair :: TermName
termFunction = TermNotion [Word ["function"], Nm]
termMap = TermNotion [Word ["map"], Nm]
termSet = TermNotion [Word ["set"], Nm]
termClass = TermNotion [Word ["class"], Nm]
termObject = TermNotion [Word ["object"], Nm]
termElement = TermNotion [Word ["element"], Nm, Word ["of"], Vr]
termApplication = TermThe [Word ["value"], Word["of"], Vr, Word ["under"], Vr]
termDomain = TermThe [Word ["domain"], Word["of"], Vr]
termPair = TermThe [Word ["ordered"], Word["pair"], Word["of"], Vr, Word ["and"], Vr]

instance Presentation TermName where
  present (TermSymbolic patterns) = showSymbolPattern patterns
  present (TermNotion patterns) = "a" <> showWordPattern patterns
  present (TermThe patterns) = "the" <> showWordPattern patterns
  present (TermUnaryAdjective patterns) = "is" <> showWordPattern patterns
  present (TermMultiAdjective patterns) = "mis" <> showWordPattern patterns
  present (TermUnaryVerb patterns) = "do" <> showWordPattern patterns
  present (TermMultiVerb patterns) = "mdo" <> showWordPattern patterns
  present (TermTask n) = "tsk_" <> show_text n
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
