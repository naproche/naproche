(*
Authors: Makarius (2018)

Build Isabelle/Naproche modules.
*)

theory Build
  imports Pure Haskell.Haskell
begin

section \<open>Isabelle/Haskell modules\<close>

ML_command \<open>
  Generated_Files.write \<^theory>\<open>Haskell\<close> (Path.append \<^master_dir> \<^path>\<open>src/Isabelle\<close>)
\<close>


section \<open>Isabelle/Scala modules\<close>

external_file "file_format.scala"

ML_command \<open>
  Isabelle_System.with_tmp_dir "scalac" (fn tmp_dir =>
    let
      val bash_paths = Bash.strings o map (File.platform_path o Path.append \<^master_dir>);
      val sources = [\<^path>\<open>file_format.scala\<close>];
      val target = \<^path>\<open>naproche.jar\<close>;
      val (out, rc) =
        Isabelle_System.bash_output
          ("cd " ^ File.bash_path tmp_dir ^ " && \
           \isabelle scalac $ISABELLE_SCALAC_OPTIONS " ^ bash_paths sources ^ " && \
           \isabelle_jdk jar cf " ^ bash_paths [target] ^ " *");
    in if rc = 0 then writeln out else error out end);
\<close>

end
