{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : SAD.Data.Terms
-- Description : TODO
-- Copyright   : (c) 2019, Anton Lorenzen
-- License     : GPL-3
module SAD.Data.Terms where

import SAD.Data.Pattern


-- * Term Names

data TermName
  = TermSymbolic SymbolPattern
  | TermNotion NotionPattern
  | TermThe NotionPattern
  | TermUnaryAdjective PredicatePattern
  | TermMultiAdjective PredicatePattern
  | TermUnaryVerb PredicatePattern
  | TermMultiVerb PredicatePattern
  | TermTask Int
  | TermEquality
  | TermLess
  | TermThesis
  deriving (Eq, Ord, Show)

termFunction, termMap, termSet, termClass, termElement, termObject,
  termApplication, termDomain, termPair :: TermName
termFunction = TermNotion [NotionWord ["function"], NotionName]
termMap = TermNotion [NotionWord ["map"], NotionName]
termSet = TermNotion [NotionWord ["set"], NotionName]
termClass = TermNotion [NotionWord ["class"], NotionName]
termObject = TermNotion [NotionWord ["object"], NotionName]
termElement = TermNotion [NotionWord ["element"], NotionName, NotionWord ["of"], NotionVar]
termApplication = TermThe [NotionWord ["value"], NotionWord["of"], NotionVar, NotionWord ["under"], NotionVar]
termDomain = TermThe [NotionWord ["domain"], NotionWord["of"], NotionVar]
termPair = TermThe [NotionWord ["ordered"], NotionWord["pair"], NotionWord["of"], NotionVar, NotionWord ["and"], NotionVar]

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
