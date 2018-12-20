(*
Authors: Makarius (2018)

Isabelle Prover IDE support for NaProChe / ForTheL.
*)

theory Naproche
  imports Pure
  keywords "forthel" :: thy_decl
    and "forthel_file" :: thy_load
begin

ML_file "naproche.ML"


generate_file "Isabelle/Naproche.hs" = \<open>
{-
Authors: Makarius (2018)

String constants for Isabelle/Naproche.
-}

module Isabelle.Naproche
where

-- options

forthel_prove, forthel_check, forthel_skipfail :: String
forthel_prove = \<open>\<^system_option>\<open>forthel_prove\<close>\<close>
forthel_check = \<open>\<^system_option>\<open>forthel_check\<close>\<close>
forthel_skipfail = \<open>\<^system_option>\<open>forthel_skipfail\<close>\<close>


-- environment

naproche_pide, naproche_pos_file, naproche_pos_shift :: String
naproche_pide = \<open>Naproche.NAPROCHE_PIDE\<close>
naproche_pos_file = \<open>Naproche.NAPROCHE_POS_FILE\<close>
naproche_pos_shift = \<open>Naproche.NAPROCHE_POS_SHIFT\<close>


-- message origin

origin, origin_main, origin_export, origin_forthel, origin_parser,
  origin_reasoner, origin_simplifier, origin_thesis :: String
origin = \<open>Naproche.origin\<close>
origin_main = \<open>Naproche.origin_main\<close>
origin_export = \<open>Naproche.origin_export\<close>
origin_forthel = \<open>Naproche.origin_forthel\<close>
origin_parser = \<open>Naproche.origin_parser\<close>
origin_reasoner = \<open>Naproche.origin_reasoner\<close>
origin_simplifier = \<open>Naproche.origin_simplifier\<close>
origin_thesis = \<open>Naproche.origin_thesis\<close>


-- server commands

command_args :: String
command_args = \<open>Naproche.command_args\<close>

forthel_command :: String
forthel_command = \<open>Naproche.forthel_command\<close>
\<close>

end
