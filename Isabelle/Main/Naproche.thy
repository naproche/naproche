(*
Authors: Makarius (2018, 2021)

Isabelle Prover IDE support for NaProChe / ForTheL.
*)

theory Naproche
  imports Main
  keywords "forthel" "forthel_tex" :: thy_decl
    and "forthel_file" :: thy_load
begin

ML_file \<open>naproche.ML\<close>


generate_file "Isabelle/Naproche.hs" = \<open>
{-
Authors: Makarius (2021)

Constants for Isabelle/Naproche.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Naproche
where

import Isabelle.Bytes (Bytes)


-- options

naproche_prove, naproche_check, naproche_skipfail :: Bytes
naproche_prove = \<open>\<^system_option>\<open>naproche_prove\<close>\<close>
naproche_check = \<open>\<^system_option>\<open>naproche_check\<close>\<close>
naproche_skipfail = \<open>\<^system_option>\<open>naproche_skipfail\<close>\<close>

naproche_pos_id, naproche_pos_file, naproche_pos_shift :: Bytes
naproche_pos_id = \<open>\<^system_option>\<open>naproche_pos_id\<close>\<close>
naproche_pos_file = \<open>\<^system_option>\<open>naproche_pos_file\<close>\<close>
naproche_pos_shift = \<open>\<^system_option>\<open>naproche_pos_shift\<close>\<close>


-- programs in Haskell
-- (see \<^file>\<open>$NAPROCHE_HOME/src/SAD/Main.hs\<close>)

cancel_program :: Bytes
cancel_program = \<open>Naproche.cancel_program\<close>

forthel_program :: Bytes
forthel_program = \<open>Naproche.forthel_program\<close>


-- commands in ML

threads_command :: Bytes
threads_command = \<open>\<^naproche_command>\<open>threads\<close>\<close>

output_state_command, output_writeln_command, output_information_command,
  output_tracing_command, output_warning_command, output_legacy_feature_command,
  output_error_command, output_report_command :: Bytes
output_state_command = \<open>\<^naproche_command>\<open>output_state\<close>\<close>
output_writeln_command = \<open>\<^naproche_command>\<open>output_writeln\<close>\<close>
output_information_command = \<open>\<^naproche_command>\<open>output_information\<close>\<close>
output_tracing_command = \<open>\<^naproche_command>\<open>output_tracing\<close>\<close>
output_warning_command = \<open>\<^naproche_command>\<open>output_warning\<close>\<close>
output_legacy_feature_command = \<open>\<^naproche_command>\<open>output_legacy_feature\<close>\<close>
output_error_command = \<open>\<^naproche_command>\<open>output_error\<close>\<close>
output_report_command = \<open>\<^naproche_command>\<open>output_report\<close>\<close>


-- prover server
-- (see \<^file>\<open>$NAPROCHE_HOME/Isabelle/src/scala/prover_server.scala\<close>)

prover_args :: Bytes
prover_args = "prover_args"

prover_command :: Bytes
prover_command = "prover"

prover_name :: Bytes
prover_name = "name"

prover_timeout :: Bytes
prover_timeout = "timeout"

prover_result :: Bytes
prover_result = "result"

prover_return_code :: Bytes
prover_return_code = "return_code"

kill_command :: Bytes
kill_command = "kill"
\<close>

end
