(*
Authors: Makarius (2018)

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


-- message origin

origin, origin_main, origin_export, origin_forthel, origin_parser,
  origin_reasoner, origin_simplifier, origin_thesis, origin_translate :: Bytes
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
-- (see \<^file>\<open>$NAPROCHE_HOME/Isabelle/src/scala/prover_server.scala\<close>)

prover_args :: Bytes
prover_args = \<open>Naproche.prover_args\<close>

uuid_command :: Bytes
uuid_command = \<open>Naproche.uuid_command\<close>

cancel_command :: Bytes
cancel_command = \<open>Naproche.cancel_command\<close>

forthel_command :: Bytes
forthel_command = \<open>Naproche.forthel_command\<close>


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
