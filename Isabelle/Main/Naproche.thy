(*
Authors: Makarius (2018)

Isabelle Prover IDE support for NaProChe / ForTheL.
*)

theory Naproche
  imports Pure
  keywords "forthel" "forthel_tex" :: thy_decl
    and "forthel_file" :: thy_load
begin

ML_file \<open>naproche.ML\<close>


generate_file "Isabelle/Naproche.hs" = \<open>
{-
Authors: Makarius (2018)

String constants for Isabelle/Naproche.
-}

module Isabelle.Naproche
where

-- options

naproche_prove, naproche_check, naproche_skipfail :: String
naproche_prove = \<open>\<^system_option>\<open>naproche_prove\<close>\<close>
naproche_check = \<open>\<^system_option>\<open>naproche_check\<close>\<close>
naproche_skipfail = \<open>\<^system_option>\<open>naproche_skipfail\<close>\<close>


-- environment

naproche_pide, naproche_pos_file, naproche_pos_shift :: String
naproche_pide = \<open>Naproche.NAPROCHE_PIDE\<close>
naproche_pos_file = \<open>Naproche.NAPROCHE_POS_FILE\<close>
naproche_pos_shift = \<open>Naproche.NAPROCHE_POS_SHIFT\<close>


-- message origin

origin, origin_main, origin_export, origin_forthel, origin_parser,
  origin_reasoner, origin_simplifier, origin_thesis, origin_translate :: String
origin = \<open>Naproche.origin\<close>
origin_main = \<open>Naproche.origin_main\<close>
origin_export = \<open>Naproche.origin_export\<close>
origin_forthel = \<open>Naproche.origin_forthel\<close>
origin_parser = \<open>Naproche.origin_parser\<close>
origin_reasoner = \<open>Naproche.origin_reasoner\<close>
origin_simplifier = \<open>Naproche.origin_simplifier\<close>
origin_thesis = \<open>Naproche.origin_thesis\<close>
origin_translate = \<open>Naproche.origin_translate\<close>


-- server commands
-- (see \<^file>\<open>$NAPROCHE_HOME/src/SAD/Main.hs\<close>)
-- (see \<^file>\<open>$NAPROCHE_HOME/Isabelle/prover_server.scala\<close>)

command_args :: String
command_args = \<open>Naproche.command_args\<close>

cancel_command :: String
cancel_command = \<open>Naproche.cancel_command\<close>

forthel_command :: String
forthel_command = \<open>Naproche.forthel_command\<close>


prover_command :: String
prover_command = "prover"

prover_name :: String
prover_name = "name"

prover_timeout :: String
prover_timeout = "timeout"

prover_result :: String
prover_result = "result"

prover_return_code :: String
prover_return_code = "return_code"

kill_command :: String
kill_command = "kill"
\<close>

end
