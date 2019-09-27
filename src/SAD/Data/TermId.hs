module SAD.Data.TermId where

import Debug.Trace

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
  | SpecialId Int -- TODO: This seems unnecessary..
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