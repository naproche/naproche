{-
Authors: Andrei Paskevich (2001 - 2008), Steffen Frerix (2017 - 2018)

Construct prover database.
-}

{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module SAD.Core.Provers (Prover(..), readProverDatabase) where

import Data.Yaml
import qualified SAD.Core.Message as Message
import SAD.Core.SourcePos
import GHC.Generics
import Data.Bifunctor
import qualified Data.ByteString as B

data Prover = Prover {
  name           :: String,
  label          :: String,
  path           :: String,
  arguments      :: [String],
  successMessage :: [String],
  contradictionMessage :: [String],
  failureMessage :: [String],
  unknownMessage :: [String] }
  deriving (Eq, Ord, Show, Generic)

instance FromJSON Prover

readProverDatabase :: Message.Comm m => FilePath -> B.ByteString -> m [Prover]
readProverDatabase path txt = do
  let yamlEither = first prettyPrintParseException $ decodeEither' txt
  case yamlEither >>= mapM validate of
    Right r -> pure r
    Left l -> err l
  where
    err = Message.errorExport (fileOnlyPos path)

validate :: Prover -> Either String Prover
validate Prover { name = n, path = "" }
  = Left $ " prover '" ++ n ++ "' has no command line"
validate Prover { name = n, successMessage = [] }
  = Left $ " prover '" ++ n ++ "' has no success responses"
validate Prover { name = n, failureMessage = [], unknownMessage = [] }
  = Left $ " prover '" ++ n ++ "' has no failure responses"
validate r = Right r
