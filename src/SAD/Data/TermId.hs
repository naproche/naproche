module SAD.Data.TermId where

import Data.Map (Map)

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
specialId n = case n of
  ( -1) -> EqualityId
  ( -2) -> LessId
  ( -3) -> ThesisId
  ( -4) -> FunctionId
  ( -5) -> ApplicationId
  ( -6) -> DomainId
  ( -7) -> SetId
  ( -8) -> ElementId
  ( -9) -> ProductId
  (-10) -> PairId
  (-11) -> ObjectId
  (-15) -> NewId
  n -> SpecialId n