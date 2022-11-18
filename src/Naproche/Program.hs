-- |
-- Authors: Makarius Wenzel (2021)
--
-- Naproche program context: Console or PIDE.


module Naproche.Program (
  Context, console, is_pide, check_pide,
  write_message, read_message, exchange_message, exchange_message0,
  get_options, bool_option, int_option, string_option, is_isabelle,
  adjust_position, pide_command, yxml_pide_command,
  exit_thread, init_console, init_pide, thread_context,
  Error (..), print_error, error,
  serials, serial
) where

import Prelude hiding (error)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.IORef (IORef)
import Data.IORef qualified as IORef
import System.IO.Unsafe (unsafePerformIO)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.ByteString.Char8 qualified as Char8
import Control.Concurrent (ThreadId)
import Control.Monad (when, unless, replicateM)
import Control.Concurrent qualified as Concurrent
import Control.Exception qualified as Exception
import Control.Exception (Exception)
import Network.Socket (Socket)

import Isabelle.Bytes qualified as Bytes
import Isabelle.Bytes (Bytes)
import Isabelle.Byte_Message qualified as Byte_Message
import Isabelle.Value qualified as Value
import Isabelle.Position qualified as Position
import Isabelle.Options qualified as Options
import Isabelle.XML.Encode qualified as Encode
import Isabelle.XML.Decode qualified as Decode
import Isabelle.YXML qualified as YXML
import Isabelle.Naproche qualified as Naproche
import Isabelle.Library


{- program context -}

data Context = Console | PIDE Socket Options.T

console :: Context
console = Console

instance Show Context where
  show Console = "Console"
  show (PIDE _ _) = "PIDE"

is_pide :: Context -> Bool
is_pide Console = False
is_pide (PIDE _ _) = True

check_pide :: Applicative f => Context -> f ()
check_pide context =
  unless (is_pide context) $ errorWithoutStackTrace "No PIDE context"

write_message :: Context -> [Bytes] -> IO ()
write_message Console = Char8.putStrLn . Bytes.unmake . Bytes.concat
write_message (PIDE socket _) = Byte_Message.write_message socket

read_message :: Context -> IO (Maybe [Bytes])
read_message Console = return Nothing
read_message (PIDE socket _) = Byte_Message.read_message socket

exchange_message :: Context -> [Bytes] -> IO [Bytes]
exchange_message context msg = do
  write_message context msg
  result <- read_message context
  case result of
    Nothing -> errorWithoutStackTrace "No result message: socket closed"
    Just res -> return res

exchange_message0 :: Context -> [Bytes] -> IO ()
exchange_message0 context msg = do
  write_message context msg
  _ <- read_message context
  return ()


{- options -}

get_options :: Context -> Maybe Options.T
get_options Console = Nothing
get_options (PIDE _ options) = Just options

get_option :: a -> (Options.T -> Bytes -> a) -> Context -> Bytes -> a
get_option def get context opt =
  case get_options context of
    Nothing -> def
    Just options -> get options opt

bool_option :: Context -> Bytes -> Bool
bool_option = get_option False Options.bool

int_option :: Context -> Bytes -> Int
int_option = get_option 0 Options.int

string_option :: Context -> Bytes -> Bytes
string_option = get_option Bytes.empty Options.string

is_isabelle :: Context -> Bool
is_isabelle context = bool_option context Naproche.naproche_isabelle


{- position -}

adjust_position :: Context -> Position.T -> Position.T
adjust_position Console pos = pos
adjust_position (PIDE _ options) pos =
  let
    pos_id = Options.string options Naproche.naproche_pos_id
    pos_file = Options.string options Naproche.naproche_pos_file
    pos_shift = Options.int options Naproche.naproche_pos_shift
  in
    pos
    |> Position.put_file (fromMaybe pos_file (Position.file_of pos))
    |> Position.put_id pos_id
    |> Position.shift_offsets pos_shift


{- PIDE commands -}

pide_command :: Bytes -> Context -> [Bytes] -> IO [Bytes]
pide_command command context args = do
  check_pide context
  exchange_message context (command : args)

yxml_pide_command :: Encode.T a -> Decode.T b -> Bytes -> Context -> [a] -> IO [b]
yxml_pide_command encode decode command context xs = do
  let args = map (YXML.string_of_body . encode) xs
  result <- pide_command command context args
  return $ map (decode . YXML.parse_body) result


{- program threads -}

type Threads = Map ThreadId Context

{-# NOINLINE global_threads #-}
global_threads :: IORef Threads
global_threads = unsafePerformIO (IORef.newIORef Map.empty)

update_threads :: (ThreadId -> Threads -> Threads) -> IO ()
update_threads f = do
  id <- Concurrent.myThreadId
  IORef.atomicModifyIORef' global_threads (\threads -> (f id threads, ()))

exit_thread :: IO ()
exit_thread = update_threads Map.delete

init_thread :: Context -> IO Context
init_thread context = do
  update_threads (`Map.insert` context)
  return context

init_console :: IO Context
init_console = init_thread Console

init_pide :: Socket -> Options.T -> IO Context
init_pide socket options = init_thread (PIDE socket options)

thread_context :: IO Context
thread_context = do
  id <- Concurrent.myThreadId
  threads <- IORef.readIORef global_threads
  return $ fromMaybe Console (Map.lookup id threads)


{- errors -}

newtype Error = Error Bytes
instance Exception Error

print_error :: Error -> Bytes
print_error (Error msg) = msg

instance Show Error where show = make_string . print_error

error :: Bytes -> IO a
error msg = do
  context <- thread_context
  if is_pide context then Exception.throw $ Error msg
  else errorWithoutStackTrace $ make_string msg


{- serial numbers, preferable from Isabelle/ML -}

{-# NOINLINE global_counter #-}
global_counter :: IORef Int
global_counter = unsafePerformIO (IORef.newIORef 0)

next_counter :: IO Int
next_counter = do
  IORef.atomicModifyIORef' global_counter
    (\i ->
      if i < maxBound then (i + 1, i + 1)
      else errorWithoutStackTrace "Overflow of global counter")

serials :: Context -> Int -> IO [Int]
serials context n =
  if is_pide context then
    do
      result <- exchange_message context [Naproche.serials_command, Value.print_int n]
      let res = mapMaybe Value.parse_int result
      let m = length res
      when (m /= n) $
        errorWithoutStackTrace
          ("Bad result of command \"serials\": returned " <> show m <> ", expected " <> show n)
      return res
  else replicateM n next_counter

serial :: Context -> IO Int
serial context = do
  res <- serials context 1
  return $ head res
