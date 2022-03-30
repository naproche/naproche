{-
Authors: Makarius Wenzel (2021)

External provers.
-}

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE MultiWayIf #-}

module Naproche.Prover (
  Prover, Status (..), get_name, get_args, status,
  verbose, timeout, memory_limit, by_contradiction,
  list, find, eprover, eproververb, spass, vampire,
  prover_command, get_variable,
)
where

import qualified Data.List as List
import Control.Monad (when)
import qualified Isabelle.Bytes as Bytes
import Isabelle.Bytes (Bytes)
import qualified Isabelle.Value as Value
import qualified Isabelle.Bash as Bash
import qualified Isabelle.Process_Result as Process_Result
import qualified Isabelle.Time as Time
import Isabelle.Time (Time)
import Isabelle.Library


{- type Prover -}

data Prover = Prover {
  _name :: Bytes,
  _variable :: Bytes,
  _args :: Prover -> [Bytes],
  _status :: Prover_Status,
  _messages :: Messages,

  _verbose :: Bool,
  _timeout :: Time,
  _memory_limit :: Int,
  _by_contradiction :: Bool
}

type Prover_Status = Prover -> Process_Result.T -> Status

data Status = Success | Failure | Contradictory_Axioms | Unknown | Error Bytes
  deriving Show

data Messages = Messages {
  _contradiction :: [Bytes],
  _success :: [Bytes],
  _failure :: [Bytes],
  _unknown :: [Bytes]
}

get_name :: Prover -> Bytes
get_name Prover{_name} = _name

get_variable :: Prover -> Bytes
get_variable Prover{_variable} = _variable

get_args :: Prover -> [Bytes]
get_args p = _args p p

instance Show Prover where show = make_string . get_name

make_prover :: Bytes -> Bytes -> (Prover -> [Bytes]) -> Prover_Status -> Messages -> Prover
make_prover name variable args status messages =
  Prover {
  _name = name,
  _variable = variable,
  _args = args,
  _status = status,
  _messages = messages,

  _verbose = False,
  _timeout = Time.zero,
  _memory_limit = 0,
  _by_contradiction = False
}


{- run prover -}

status :: Prover -> Process_Result.T -> Status
status prover = _status prover prover


{- prover parameters -}

verbose :: Prover -> Prover
verbose prover = prover { _verbose = True }

timeout :: Time -> Prover -> Prover
timeout timeout prover = prover { _timeout = timeout }

memory_limit :: Int -> Prover -> Prover
memory_limit memory_limit prover = prover { _memory_limit = memory_limit }

by_contradiction :: Bool -> Prover -> Prover
by_contradiction by_contradiction prover = prover { _by_contradiction = by_contradiction }
  
print_seconds :: Time -> Bytes
print_seconds = Value.print_int . round . Time.get_seconds


{- prover "methods" -}

prover_command :: Bytes -> [Bytes] -> Prover -> Bytes -> IO Bash.Params 
prover_command exe args prover input = do
  when (Bytes.null exe) $
    error $ make_string ("Cannot run prover " <> quote (_name prover) <>
      ": undefined environment variable " <> _variable prover)
  return $
    Bash.input input $
    Bash.timeout (_timeout prover) $
    Bash.script (Bash.strings (exe : args))
  
prover_status :: Prover_Status
prover_status prover result =
  let
    Messages{_success, _contradiction, _failure, _unknown} = _messages prover
    timeout = Process_Result.rc result == Process_Result.timeout_rc
    out = Process_Result.out_lines result
    err = Process_Result.err_lines result

    test msgs = any (\line -> not (Bytes.null line) && any (`Bytes.isPrefixOf` line) msgs) out
    contradictions = test _contradiction
    positive = test _success
    negative = test _failure
    inconclusive = test _unknown
  in
    if | not timeout && null out -> Error "No prover response"
       | not (timeout || positive || contradictions || negative || inconclusive) ->
          Error (cat_lines ("Bad prover response:" : out))
       | positive || (_by_contradiction prover && contradictions) -> Success
       | negative -> Failure
       | not (_by_contradiction prover) && contradictions -> Contradictory_Axioms
       | timeout || inconclusive -> Unknown
       | null err -> Error "Prover error"
       | otherwise -> Error (cat_lines ("Prover error:" : err))



{- list of provers -}

list :: [Prover]
list = [eprover, eproververb, spass, vampire]

find :: Bytes -> Maybe Prover
find name = List.find (\prover -> get_name prover == name) list


{- eprover -}

eprover :: Prover
eprover =
  make_prover "eprover" "NAPROCHE_EPROVER" eprover_command
    prover_status eprover_messages

eprover_command :: Prover -> [Bytes]
eprover_command prover = args
  where
    Prover{_verbose, _timeout, _memory_limit} = prover
    args =
      ["--auto"] ++
      [if _verbose then "--verbose" else "--silent"] ++
      ["--cpu-limit=" <> print_seconds _timeout | _timeout > Time.zero] ++
      ["--memory-limit=" <> Value.print_int _memory_limit | _memory_limit > 0]

eprover_messages :: Messages
eprover_messages = 
  Messages {
    _contradiction = ["# SZS status ContradictoryAxioms"],
    _success = ["# SZS status Theorem"],
    _failure = ["# SZS status CounterSatisfiable"],
    _unknown = ["# SZS status ResourceOut", "# SZS status GaveUp"]
  }


{- eproververb -}

eproververb :: Prover
eproververb =
  make_prover "eproververb" "NAPROCHE_EPROVER" eproververb_command
    prover_status eprover_messages

eproververb_command :: Prover -> [Bytes]
eproververb_command prover = args
  where
    Prover{_timeout, _memory_limit} = prover
    args =
      ["-xAuto", "-tAuto", "-mAuto", "--tstp-in", "-l", "2"] ++
      ["--cpu-limit=" <> print_seconds _timeout | _timeout > Time.zero] ++
      ["--memory-limit=" <> Value.print_int _memory_limit | _memory_limit > 0]

  
{- spass -}

spass :: Prover
spass =
  make_prover "spass" "NAPROCHE_SPASS" spass_command
    prover_status spass_messages

spass_command :: Prover -> [Bytes]
spass_command prover = args
  where
    Prover{_timeout, _memory_limit} = prover
    args =
      ["-TPTP", "-CNFOptSkolem=0", "-PProblem=0", "-PGiven=0", "-Stdin"] ++
      ["-TimeLimit=" <> print_seconds _timeout | _timeout > Time.zero]

spass_messages :: Messages
spass_messages =
    Messages {
      _contradiction = [],
      _success = ["SPASS beiseite: Proof found."],
      _failure = ["SPASS beiseite: Completion found."],
      _unknown = ["SPASS beiseite: Ran out of time."]
          -- "SPASS beiseite: Maximal number of loops exceeded."
    }
      
      
{- vampire -}

vampire :: Prover
vampire =
  make_prover "vampire" "NAPROCHE_VAMPIRE" vampire_command
    prover_status vampire_messages

vampire_command :: Prover -> [Bytes]
vampire_command prover = args
  where
    Prover{_timeout, _memory_limit} = prover
    args =
      ["--mode", "casc", "--bad_option", "hard"] ++
      (if _timeout > Time.zero then ["--time_limit", print_seconds _timeout <> "s"] else []) ++
      (if _memory_limit > 0 then ["--memory_limit", Value.print_int _memory_limit] else [])

vampire_messages :: Messages
vampire_messages =
  Messages {
    _contradiction = [],  -- guessed this one: "% SZS status ContradictoryAxioms for
    _success = ["% SZS output end Proof for"],
    _failure = ["% SZS status CounterSatisfiable for"],
    _unknown = ["% SZS status Timeout for"]
  }
