{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE JavaScriptFFI, CPP #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Main where

import Prelude hiding (error)
import qualified Prelude as Prelude
import Control.Monad
import Control.Monad.IO.Class
import Data.Binary (decodeOrFail, encode, Binary)
import Data.Text (Text)
import GHC.Generics
import Data.Aeson (ToJSON, FromJSON)
import Data.String (fromString)

import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Aeson as Aeson
import qualified System.Exit as Exit
import qualified System.Console.GetOpt as GetOpt

import Asterius.Types
import Asterius.Aeson

import SAD.Core.Message
import SAD.Core.Cache (CacheStorage(..), FileCache(..))
import SAD.Core.Provers (Prover(..), readProverDatabase)
import SAD.Core.Prove (RunProver(..))
import SAD.Core.Reader (HasLibrary(..), parseInit)
import SAD.Data.Instr (Instr(..), Flag(..), askFlag, Argument(..), noPos, Pos, ParserKind)
import SAD.Data.Text.Block (ProofText(..))
import SAD.Main

main :: IO ()
main  = do
  -- command line and init file
  (ConfigReceive args initOpt proversFile) <- getConfig
  let args0 = map Text.unpack args
  (opts0, pk, mFileName) <- readArgs' args0 initOpt
  let text0 = (map (uncurry ProofTextInstr) (reverse opts0) ++) $ case mFileName of
        Nothing -> Prelude.error $ "Naproche-Web does not support stdin."
        Just f -> [ProofTextInstr noPos $ GetArgument (Read pk) (Text.pack f)]
  let opts1 = map snd opts0

  if askFlag Help False opts1 then do
    output undefined undefined undefined (GetOpt.usageInfo usageHeader options)
  else do
    consoleMainBody opts1 text0 proversFile

readArgs' :: (MonadIO m, Comm m) => [String] -> Text -> m ([(Pos, Instr)], ParserKind, Maybe FilePath)
readArgs' args initFileContent = do
  let (instrs, files, errs) = GetOpt.getOpt GetOpt.Permute options args
  unless (null errs) $ errorWithoutStackTrace (unlines errs)
  initFile <- parseInit "init.opt" initFileContent

  let initialOpts = initFile ++ map (noPos,) instrs
  readArgs initialOpts files

consoleMainBody :: [Instr] -> [ProofText] -> Text -> IO ()
consoleMainBody opts0 text0 proversFile = do
  provers <- readProverDatabase "provers.json" $ Text.encodeUtf8 proversFile
  exit <- mainBody provers opts0 text0
  Exit.exitWith exit

foreign import javascript unsafe "sendMessage" sendMessage' :: JSVal -> IO ()
foreign import javascript unsafe "requestMessage" requestMessage' :: JSVal -> IO JSVal

sendMessage :: ToJSON a => a -> IO ()
sendMessage = sendMessage' . jsonToJSVal

requestMessage :: (ToJSON a, FromJSON b) => a -> IO (Maybe b)
requestMessage m = do
  msg <- requestMessage' $ jsonToJSVal m
  case jsonFromJSVal msg of
    Right r -> pure $ Just r
    Left _ -> pure Nothing

removePrefix :: String -> Aeson.Options
removePrefix prefix = Aeson.defaultOptions
  { Aeson.fieldLabelModifier = drop (length prefix) }

data ConfigSend = ConfigSend
  { configReq :: Text
  } deriving (Generic, Show)

instance ToJSON ConfigSend where
  toJSON     = Aeson.genericToJSON (removePrefix "config")
  toEncoding = Aeson.genericToEncoding (removePrefix "config")

data ConfigReceive = ConfigReceive
  { args :: [Text]
  , initFile :: Text
  , proversFile :: Text
  } deriving (Generic, Show)

instance FromJSON ConfigReceive

getConfig :: IO ConfigReceive
getConfig = do
  resp <- requestMessage $ ConfigSend "config"
  case resp of
    Nothing -> Prelude.error $ "Config malformed!"
    Just c -> pure c

data CommSend = CommSend
  { commReq :: Text
  , commMsg :: Text
  } deriving (Generic, Show)

instance ToJSON CommSend where
  toJSON     = Aeson.genericToJSON (removePrefix "comm")
  toEncoding = Aeson.genericToEncoding (removePrefix "comm")

instance Comm IO where
  output _ _ _ msg = do
    sendMessage $ CommSend "output" (Text.pack msg)
  
  error _ _ msg = do
    sendMessage $ CommSend "error" (Text.pack msg)
    Prelude.error $ "Naproche terminated: " ++ msg

  reportsString _ = pure ()
  pideContext = pure Nothing
  textFieldWidth = pure 120

data CacheSend = CacheSend
  { cacheReq :: Text
  , cacheFileName :: Text
  , cacheFileContent :: Text
  } deriving (Show, Generic)

instance ToJSON CacheSend where
  toJSON     = Aeson.genericToJSON (removePrefix "cache")
  toEncoding = Aeson.genericToEncoding (removePrefix "cache")

data CacheReceive = CacheReceive
  { cacheContent :: Text
  } deriving (Show, Generic)

instance FromJSON CacheReceive

decodeMay :: Binary a => BS.ByteString -> Maybe a
decodeMay bs = case decodeOrFail bs of
  Left _ -> Nothing
  Right (_, _, a) -> Just a

instance CacheStorage IO where
  readFileCache f = do
    resp <- requestMessage $ CacheSend "read" (Text.pack f) ""
    case decodeMay . BS.fromStrict . Text.encodeUtf8 . cacheContent =<< resp of
      Nothing -> pure mempty
      Just c -> pure c { lastRun = 1 + lastRun c }

  writeFileCache f c = do
    sendMessage $ CacheSend "write" (Text.pack f) (Text.decodeUtf8 $ BS.toStrict $ encode c)

data ReadLibrarySend = ReadLibrarySend
  { readReq :: Text
  , readFileName :: Text
  } deriving (Show, Generic)

instance ToJSON ReadLibrarySend where
  toJSON     = Aeson.genericToJSON (removePrefix "read")
  toEncoding = Aeson.genericToEncoding (removePrefix "read")

data ReadLibraryReceive = ReadLibraryReceive
  { fileContent :: Text
  } deriving (Show, Generic)

instance FromJSON ReadLibraryReceive

instance HasLibrary IO where
  readLibrary f = do
    resp <- requestMessage $ ReadLibrarySend "library" (Text.pack f)
    case resp of
      Just t -> pure (f, fileContent t)
      _ -> Prelude.error $ "Ensure in JS that this never happens!"

data RunProverSend = RunProverSend
  { proverReq :: Text
  , proverPath :: Text
  , proverArgs :: [Text]
  , proverTask :: Text
  } deriving (Show, Generic)

instance ToJSON RunProverSend where
  toJSON     = Aeson.genericToJSON (removePrefix "prover")
  toEncoding = Aeson.genericToEncoding (removePrefix "prover")

data RunProverReceive = RunProverReceive
  { proverOut :: Text
  } deriving (Show, Generic)

instance FromJSON RunProverReceive

instance RunProver IO where
  runProver _ (Prover _ _ path args _ _ _ _) _ timeLimit memoryLimit task = do
    let req = RunProverSend "prover" (Text.pack path)
          (map (Text.pack . setLimits timeLimit memoryLimit) args) task
    resp <- requestMessage req
    case resp of
      Just t -> pure (0, proverOut t)
      _ -> Prelude.error $ "Ensure in JS that this never happens!"

setLimits :: Int -> Int -> String -> String
setLimits timeLimit memoryLimit = go
  where
    go ('%':'t':rs) = show timeLimit ++ go rs
    go ('%':'m':rs) = show memoryLimit ++ go rs
    go (s:rs) = s : go rs
    go [] = []
