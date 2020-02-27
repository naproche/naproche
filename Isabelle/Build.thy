(*
Authors: Makarius Wenzel (2018)

Build Isabelle/Naproche modules.
*)

theory Build
  imports Pure Haskell.Haskell Naproche.Naproche
begin

section \<open>Isabelle/Haskell modules\<close>

export_generated_files _ (in Haskell) and _ (in Naproche)


section \<open>Isabelle/Scala modules\<close>

external_file \<open>file_format.scala\<close>

compile_generated_files
  external_files \<open>file_format.scala\<close>
  export_files \<open>naproche.jar\<close>
  where \<open>fn dir =>
    ignore (Generated_Files.execute dir \<open>Build\<close>
      "isabelle scalac $ISABELLE_SCALAC_OPTIONS file_format.scala && \
      \isabelle_jdk jar cf naproche.jar *")\<close>

end
