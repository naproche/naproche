module PIDE.Server where

import Network.Socket (Socket)
import qualified Control.Exception as Exception

import qualified Data.ByteString.UTF8 as UTF8
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Naproche as Naproche
import qualified Isabelle.Properties as Properties
import qualified Isabelle.Standard_Thread as Standard_Thread
import qualified Isabelle.UUID as UUID
import qualified Isabelle.XML as XML
import qualified Isabelle.YXML as YXML

import PIDE.Message
import PIDE.SourcePos

serverConnection :: (Maybe String -> String -> IO ()) -> Socket -> IO ()
serverConnection action connection = do
  thread_uuid <- Standard_Thread.my_uuid
  mapM_ (Byte_Message.write_line_message connection . UUID.bytes) thread_uuid

  res <- Byte_Message.read_line_message connection
  case fmap (YXML.parse . UTF8.toString) res of
    Just (XML.Elem ((command, _), body)) | command == Naproche.cancel_command ->
      mapM_ Standard_Thread.stop_uuid (UUID.parse_string (XML.content_of body))

    Just (XML.Elem ((command, props), body)) | command == Naproche.forthel_command ->
      Exception.bracket_ (initThread props (Byte_Message.write connection))
        exitThread
        (do
          Exception.catch (action (Properties.get props Naproche.command_args) (XML.content_of body))
            (\err -> do
              let msg = Exception.displayException (err :: Exception.SomeException)
              Exception.catch
                (if YXML.detect msg then
                  Byte_Message.write connection [UTF8.fromString msg]
                 else outputMain ERROR noSourcePos msg)
                (\(err2 :: Exception.IOException) -> pure ())))

    _ -> return ()