{-# LANGUAGE OverloadedStrings #-}

module SAD.Data.Terms where

import Debug.Trace
import Data.Text (Text)
import qualified Data.Text as Text
import SAD.Export.Representation

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

instance Representation TermName where
  represent (TermName t) =  t
  represent (TermSymbolic t) = "s" <>  t
  represent (TermNotion t) = "a" <>  t
  represent (TermThe t) = "the" <>  t
  represent (TermUnaryAdjective t) = "is" <>  t
  represent (TermMultiAdjective t) = "mis" <>  t
  represent (TermUnaryVerb t) = "do" <>  t
  represent (TermMultiVerb t) = "mdo" <>  t
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