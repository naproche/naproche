{-# LANGUAGE ExistentialQuantification #-}

{-
Authors: Makarius Wenzel (2021)

Naproche program context: Console or PIDE.
-}

module Naproche.Program (
  MessageExchangeContext(..), RunProverContext(..), Console(..),
  check_pide, exchange_message, exchange_message0,
  bool_option, int_option, string_option, is_isabelle,
  adjust_position, pide_command, yxml_pide_command,
  exit_thread, init_console, init_thread, thread_context,
  Error (..), print_error, error,
  serials, serial
)
where

import Prelude hiding (error)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.IORef (IORef)
import qualified Data.IORef as IORef
import System.IO.Unsafe (unsafePerformIO)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.ByteString.Char8 as Char8
import Control.Concurrent (ThreadId)
import Control.Monad (when, unless, replicateM)
import qualified Control.Concurrent as Concurrent
import qualified Control.Exception as Exception
import Control.Exception (Exception)

import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Value as Value
import qualified Isabelle.Position as Position
import qualified Isabelle.Options as Options
import qualified Isabelle.XML.Encode as Encode
import qualified Isabelle.XML.Decode as Decode
import qualified Isabelle.YXML as YXML
import qualified Isabelle.Naproche as Naproche
import Isabelle.Library
import qualified Isabelle.Process_Result as Process_Result
import qualified Isabelle.Bash as Bash
import qualified Naproche.System as System

{- program context -}

class MessageExchangeContext context where
  write_message :: context -> [Bytes] -> IO ()
  read_message :: context -> IO (Maybe [Bytes])
  is_pide :: context -> Bool
  get_options :: context -> Maybe Options.T

class RunProverContext c where
  runProver :: c -> Bash.Params -> IO Process_Result.T

{- console context -}

data Console = Console

instance MessageExchangeContext Console where
  read_message Console = return Nothing
  write_message Console = Char8.putStrLn . Bytes.unmake . Bytes.concat
  is_pide Console = False
  get_options Console = Nothing

instance RunProverContext Console where
  runProver _ = System.bash_process

check_pide :: (MessageExchangeContext context, Applicative f) => context -> f ()
check_pide context =
  unless (is_pide context) $ errorWithoutStackTrace "No PIDE context"

exchange_message :: MessageExchangeContext context => context -> [Bytes] -> IO [Bytes]
exchange_message context msg = do
  write_message context msg
  result <- read_message context
  case result of
    Nothing -> errorWithoutStackTrace "No result message: socket closed"
    Just res -> return res

exchange_message0 :: MessageExchangeContext context => context -> [Bytes] -> IO ()
exchange_message0 context msg = do
  write_message context msg
  _ <- read_message context
  return ()


{- options -}

get_option :: MessageExchangeContext context => a -> (Options.T -> Bytes -> a) -> context -> Bytes -> a
get_option def get context opt =
  case get_options context of
    Nothing -> def
    Just options -> get options opt

bool_option :: MessageExchangeContext context => context -> Bytes -> Bool
bool_option = get_option False Options.bool

int_option :: MessageExchangeContext context => context -> Bytes -> Int
int_option = get_option 0 Options.int

string_option :: MessageExchangeContext context => context -> Bytes -> Bytes
string_option = get_option Bytes.empty Options.string

is_isabelle :: MessageExchangeContext context => context -> Bool
is_isabelle context = bool_option context Naproche.naproche_isabelle


{- position -}

adjust_position :: MessageExchangeContext context => context -> Position.T -> Position.T
adjust_position context pos =
  case get_options context of
    Nothing -> pos
    Just options -> 
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

pide_command :: MessageExchangeContext context => Bytes -> context -> [Bytes] -> IO [Bytes]
pide_command command context args = do
  check_pide context
  exchange_message context (command : args)

yxml_pide_command :: MessageExchangeContext context => Encode.T a -> Decode.T b -> Bytes -> context -> [a] -> IO [b]
yxml_pide_command encode decode command context xs = do
  let args = map (YXML.string_of_body . encode) xs
  result <- pide_command command context args
  return $ map (decode . YXML.parse_body) result


{- program threads -}

data ThreadContext = forall context. (MessageExchangeContext context, RunProverContext context) =>
  ThreadContext context

instance MessageExchangeContext ThreadContext where
  write_message (ThreadContext c) = write_message c
  read_message (ThreadContext c) = read_message c
  is_pide (ThreadContext c) = is_pide c
  get_options (ThreadContext c) = get_options c

instance RunProverContext ThreadContext where
  runProver (ThreadContext c) = runProver c

type Threads = Map ThreadId ThreadContext

{-# NOINLINE global_threads #-}
global_threads :: IORef Threads
global_threads = unsafePerformIO (IORef.newIORef Map.empty)

update_threads :: (ThreadId -> Threads -> Threads) -> IO ()
update_threads f = do
  id <- Concurrent.myThreadId
  IORef.atomicModifyIORef' global_threads (\threads -> (f id threads, ()))

exit_thread :: IO ()
exit_thread = update_threads Map.delete
    
init_thread :: (MessageExchangeContext context, RunProverContext context) => context -> IO context
init_thread context = do
  update_threads (`Map.insert` ThreadContext context)
  return context

init_console :: IO Console
init_console = init_thread Console

thread_context :: IO ThreadContext
thread_context = do
  id <- Concurrent.myThreadId
  threads <- IORef.readIORef global_threads
  return $ fromMaybe (ThreadContext Console) (Map.lookup id threads)


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

serials :: MessageExchangeContext context => context -> Int -> IO [Int]
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

serial :: MessageExchangeContext context => context -> IO Int
serial context = do
  res <- serials context 1
  return $ head res
