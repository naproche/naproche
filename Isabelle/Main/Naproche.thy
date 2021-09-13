(*
Authors: Makarius (2018, 2021)

Isabelle Prover IDE and logic support for NaProChe / ForTheL.
*)

theory Naproche
  imports Main
  keywords "forthel" "forthel_tex" :: thy_decl
    and "forthel_file" :: thy_load
begin


section \<open>Logic\<close>

typedecl i  \<comment> \<open>individuals of ``untyped'' HOL\<close>

axiomatization
  \<comment> \<open>primitive adjectives\<close>
  setsized :: \<open>i \<Rightarrow> bool\<close> and  \<comment> \<open>``small'' sets\<close>

  \<comment> \<open>primitive notions\<close>
  Fun :: \<open>i \<Rightarrow> bool\<close>  \<comment> \<open>functions\<close> and
  Set :: \<open>i \<Rightarrow> bool\<close>  \<comment> \<open>sets\<close> and
  Class :: \<open>i \<Rightarrow> bool\<close>  \<comment> \<open>classes\<close> and
  Elem :: \<open>i \<Rightarrow> i \<Rightarrow> bool\<close>  \<comment> \<open>set membership / elements of a set\<close> and
  Obj :: \<open>i \<Rightarrow> bool\<close>  \<comment> \<open>objects\<close> and

  \<comment> \<open>primitive predicates\<close>
  Less :: \<open>i \<Rightarrow> i \<Rightarrow> bool\<close>  \<comment> \<open>relation for induction\<close> and

  \<comment> \<open>primitive operations\<close>
  Dom :: \<open>i \<Rightarrow> i\<close> and
  Prod :: \<open>i \<Rightarrow> i \<Rightarrow> i\<close> and
  Pair :: \<open>i \<Rightarrow> i \<Rightarrow> i\<close> and
  App :: \<open>i \<Rightarrow> i \<Rightarrow> i\<close> and

  Thesis :: \<open>bool\<close> and
  This :: 'a

notation (output)
  Elem (infix \<open>\<^bold>\<in>\<close> 50) and
  Less (infix \<open>\<prec>\<close> 50) and
  Prod (infix \<open>\<times>\<close> 20) and
  Pair (\<open>\<langle>_,/ _\<rangle>\<close> [0, 0] 1000) and
  App (infix \<open>\<cdot>\<close> 90)


section \<open>Isabelle/ML\<close>

ML_file \<open>naproche.ML\<close>


section \<open>Isabelle/Haskell\<close>

generate_file "Isabelle/Naproche.hs" = \<open>
{-
Authors: Makarius (2021)

Constants for Isabelle/Naproche.
-}

{-# LANGUAGE OverloadedStrings #-}

module Isabelle.Naproche (
  naproche_prove, naproche_check, naproche_skipfail,
  naproche_pos_id, naproche_pos_file, naproche_pos_shift,
  naproche_isabelle,

  cancel_program, forthel_program,

  threads_command, serials_command, cert_terms_command, print_terms_command,
  print_sequents_command,

  output_state_command, output_writeln_command, output_information_command,
  output_tracing_command, output_warning_command, output_legacy_feature_command,
  output_error_command, output_report_command,

  iT, is_iT, mk_this, dest_this,

  setsized_const, fun_const, set_const, class_const, elem_const, obj_const,
  less_const, dom_const, prod_const, pair_const, app_const, thesis_const
)
where

import Isabelle.Term
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

naproche_isabelle :: Bytes
naproche_isabelle = \<open>\<^system_option>\<open>naproche_isabelle\<close>\<close>


-- programs in Haskell
-- (see \<^file>\<open>$NAPROCHE_HOME/src/SAD/Main.hs\<close>)

cancel_program :: Bytes
cancel_program = \<open>Naproche.cancel_program\<close>

forthel_program :: Bytes
forthel_program = \<open>Naproche.forthel_program\<close>


-- commands in ML

threads_command, serials_command, cert_terms_command, print_terms_command,
  print_sequents_command :: Bytes
threads_command = \<open>\<^naproche_command>\<open>threads\<close>\<close>
serials_command = \<open>\<^naproche_command>\<open>serials\<close>\<close>
cert_terms_command = \<open>\<^naproche_command>\<open>cert_terms\<close>\<close>
print_terms_command = \<open>\<^naproche_command>\<open>print_terms\<close>\<close>
print_sequents_command = \<open>\<^naproche_command>\<open>print_sequents\<close>\<close>

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


-- logic

iT :: Typ; is_iT :: Typ -> Bool
(iT, is_iT) = type_op0 \<open>\<^type_name>\<open>i\<close>\<close>

mk_this :: Typ -> Term; dest_this :: Term -> Maybe Typ
(mk_this, dest_this) = typed_op0 \<open>\<^const_name>\<open>This\<close>\<close>

setsized_const, fun_const, set_const, class_const, elem_const, obj_const,
  less_const, dom_const, prod_const, pair_const, app_const, thesis_const :: Bytes
setsized_const = \<open>\<^const_name>\<open>setsized\<close>\<close>
fun_const = \<open>\<^const_name>\<open>Fun\<close>\<close>
set_const = \<open>\<^const_name>\<open>Set\<close>\<close>
class_const = \<open>\<^const_name>\<open>Class\<close>\<close>
elem_const = \<open>\<^const_name>\<open>Elem\<close>\<close>
obj_const = \<open>\<^const_name>\<open>Obj\<close>\<close>
less_const = \<open>\<^const_name>\<open>Less\<close>\<close>
dom_const = \<open>\<^const_name>\<open>Dom\<close>\<close>
prod_const = \<open>\<^const_name>\<open>Prod\<close>\<close>
pair_const = \<open>\<^const_name>\<open>Pair\<close>\<close>
app_const = \<open>\<^const_name>\<open>App\<close>\<close>
thesis_const = \<open>\<^const_name>\<open>Thesis\<close>\<close>
\<close>

end
