module PIDE where

import Prelude hiding (error)
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Char8 as Char8
import Control.Concurrent (ThreadId)
import qualified Control.Concurrent as Concurrent
import Control.Monad.State (StateT, lift)
import Control.Monad.Reader (ReaderT)
import Data.ByteString (ByteString)
import qualified Data.ByteString.UTF8 as UTF8
import qualified Isabelle.Properties as Properties
import qualified Isabelle.YXML as YXML
import qualified Isabelle.XML as XML
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Naproche as Naproche
import qualified Isabelle.Markup as Markup
import qualified Isabelle.Value as Value
import Data.IORef
import SAD.Core.Message
import SAD.Core.SourcePos
import Control.Monad
import System.Environment
import System.IO.Unsafe (unsafePerformIO)

-- PIDE thread context

type Channel = [ByteString] -> IO ()
data Context = Context {pide :: Maybe PIDE, channel :: Channel}

defaultChannel :: Channel
defaultChannel = Char8.putStrLn . ByteString.concat

defaultContext :: Context
defaultContext = Context Nothing defaultChannel


-- global state

type Threads = Map ThreadId Context

{-# NOINLINE globalState #-}
globalState :: IORef Threads
globalState = unsafePerformIO (newIORef Map.empty)

getContext :: IO Context
getContext = do
  id <- Concurrent.myThreadId
  threads <- readIORef globalState
  return (fromMaybe defaultContext (Map.lookup id threads))

updateState :: (ThreadId -> Threads -> Threads) -> IO ()
updateState f = do
  id <- Concurrent.myThreadId
  atomicModifyIORef' globalState (\threads -> (f id threads, ()))

-- init/exit thread context

initThread :: Properties.T -> Channel -> IO ()
initThread props channel = do
  updateState (\id -> Map.insert id (Context pideContext channel))
  where
    property parse = Properties.get_value parse props
    pideProperty = property (\x -> guard (not $ null x) >> pure x) Naproche.naproche_pide
    fileProperty = property Just Naproche.naproche_pos_file
    shiftProperty = property Value.parse_int Naproche.naproche_pos_shift
    pideContext =
      case (pideProperty, fileProperty, shiftProperty) of
        (Just pide, Just file, Just shift) -> Just (PIDE pide file shift)
        _ -> Nothing

exitThread :: IO ()
exitThread = updateState Map.delete

consoleThread :: IO ()
consoleThread = do
  env <- getEnvironment
  initThread env defaultChannel


-- PIDE messages

instance Comm m => Comm (StateT s m) where
  output a b c d = lift $ output a b c d
  error a b c = lift $ error a b c
  reportsString = lift . reportsString
  pideContext = lift pideContext

instance Comm m => Comm (ReaderT s m) where
  output a b c d = lift $ output a b c d
  error a b c = lift $ error a b c
  reportsString = lift . reportsString
  pideContext = lift pideContext

instance Comm IO where
  output origin kind pos msg = do
    context <- getContext
    channel context $ messageBytes (pide context) origin kind pos msg

  error origin pos msg = do
    pide <- pideContext
    errorWithoutStackTrace $
      UTF8.toString $ ByteString.concat $ messageBytes pide origin ERROR pos msg

  reportsString args = do
    context <- getContext
    when (isJust (pide context) && not (null args)) $
      channel context $ pideMessage $ YXML.string_of $
        XML.Elem (Markup.report,
          map (\((pos, markup), txt) ->
            let
              markup' = Markup.properties (posProperties (fromJust (pide context)) pos) markup
              body = if null txt then [] else [XML.Text txt]
            in XML.Elem (markup', body)) args)

  pideContext = pide <$> getContext


pideActive :: Comm m => m Bool
pideActive = isJust <$> pideContext

messageBytes :: Maybe PIDE -> String -> Kind -> SourcePos -> String -> [ByteString]
messageBytes pide origin kind pos msg =
  if isJust pide then
    pideMessage $ YXML.string_of $ xmlMessage (fromJust pide) origin kind pos msg
  else
    [UTF8.fromString
      ((if null origin then "" else "[" ++ origin ++ "] ") ++
       (case show kind of "" -> "" ; s -> s ++ ": ") ++
       (case show pos of "" -> ""; s -> s ++ "\n") ++ msg)]

xmlMessage :: PIDE -> String -> Kind -> SourcePos -> String -> XML.Tree
xmlMessage pide origin kind pos msg =
  XML.Elem ((kindXML kind, props), [XML.Text msg])
  where
    props0 = posProperties pide pos
    props = if null origin then props0 else (Naproche.origin, origin) : props0

pideMessage :: String -> [ByteString]
pideMessage = Byte_Message.make_line_message . UTF8.fromString

kindXML :: Kind -> String
kindXML STATE = Markup.stateN
kindXML WRITELN = Markup.writelnN
kindXML INFORMATION = Markup.informationN
kindXML TRACING = Markup.tracingN
kindXML WARNING = Markup.warningN
kindXML LEGACY = Markup.legacyN
kindXML ERROR = Markup.errorN