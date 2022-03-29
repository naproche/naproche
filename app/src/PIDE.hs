{-# LANGUAGE ExistentialQuantification #-}

{-
Authors: Makarius Wenzel (2021), Anton Lorenzen (2022)

Naproche program context: PIDE.
-}

module PIDE (
  PIDE, init_pide
)
where

import Network.Socket (Socket)
import qualified Isabelle.Byte_Message as Byte_Message
import qualified Isabelle.Options as Options
import qualified Isabelle.Isabelle_System as Isabelle_System
import Naproche.Program
import qualified Naproche.Prover as Prover

data PIDE = PIDE Socket Options.T

instance MessageExchangeContext PIDE where
  read_message (PIDE socket _) = Byte_Message.read_message socket
  write_message (PIDE socket _) = Byte_Message.write_message socket
  is_pide (PIDE _ _) = True
  get_options (PIDE _ options) = Just options

instance RunProverContext PIDE where
  runProver (PIDE _ options) prover input = do
    params <- Prover.prover_command (Prover.get_args prover) prover input
    Isabelle_System.bash_process options params

init_pide :: Socket -> Options.T -> IO PIDE
init_pide socket options = init_thread (PIDE socket options)