(*
Authors: Makarius Wenzel (2021)

Export Isabelle/Naproche Haskell modules.
*)

theory Build
  imports Haskell.Haskell Naproche.Naproche
begin

export_generated_files _ (in Haskell) and _ (in Naproche)

end
