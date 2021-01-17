(*
Authors: Makarius Wenzel (2021)

Build Isabelle/Naproche Haskell modules.
*)

theory Build
  imports Haskell.Haskell Naproche.Naproche
begin

section \<open>Isabelle/Haskell modules\<close>

export_generated_files _ (in Haskell) and _ (in Naproche)

end
