{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Construct prover database.
-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.Provers (Prover(..), readProverDatabase) where

import Data.Aeson
import SAD.Core.SourcePos
import SAD.Core.Message (Comm, errorExport)
import GHC.Generics
import qualified Data.ByteString as B
import Data.Text (Text)

data Prover = Prover {
  name           :: String,
  label          :: Text,
  path           :: String,
  arguments      :: [String],
  successMessage :: [Text],
  contradictionMessage :: [Text],
  failureMessage :: [Text],
  unknownMessage :: [Text] }
  deriving (Eq, Ord, Show, Generic)

instance FromJSON Prover

readProverDatabase :: Comm m => FilePath -> B.ByteString -> m [Prover]
readProverDatabase path txt = do
  case eitherDecodeStrict txt >>= mapM validate of
    Right r -> pure r
    Left l -> err l
  where
    err = errorExport (fileOnlyPos path)

validate :: Prover -> Either String Prover
validate Prover { name = n, path = "" }
  = Left $ " prover '" ++ n ++ "' has no command line"
validate Prover { name = n, successMessage = [] }
  = Left $ " prover '" ++ n ++ "' has no success responses"
validate Prover { name = n, failureMessage = [], unknownMessage = [] }
  = Left $ " prover '" ++ n ++ "' has no failure responses"
validate r = Right r
