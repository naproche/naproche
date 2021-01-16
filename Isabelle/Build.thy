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
external_file \<open>prover_server.scala\<close>

compile_generated_files
  external_files \<open>file_format.scala\<close> \<open>prover_server.scala\<close>
  export_files \<open>naproche.jar\<close>
  where \<open>fn dir =>
    ignore (Generated_Files.execute dir \<open>Build\<close>
      "isabelle scalac $ISABELLE_SCALAC_OPTIONS *.scala && \
      \isabelle_jdk jar cf naproche.jar *")\<close>

end
