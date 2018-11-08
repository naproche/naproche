(*
Authors: Makarius (2018)

Build Isabelle/Naproche modules.
*)

theory Naproche_Build
  imports Pure Haskell.Haskell
begin

section \<open>Generated Isabelle/Haskell sources\<close>

ML_command \<open>
  let
    val dir = Path.append (Resources.master_directory \<^theory>) \<^path>\<open>src/Isabelle\<close>
    val _ = Isabelle_System.mkdirs dir;
    val _ = Haskell.install_sources dir;
  in () end
\<close>


section \<open>Add-ons for Isabelle/Scala\<close>

external_file "file_format.scala"

ML_command \<open>
  Isabelle_System.with_tmp_dir "scalac" (fn tmp_dir =>
    let
      val master_dir = Resources.master_directory \<^theory>;
      val sources = [\<^path>\<open>file_format.scala\<close>];
      val target = \<^path>\<open>naproche.jar\<close>;
      val (out, rc) =
        Isabelle_System.bash_output
          ("cd " ^ File.bash_path tmp_dir ^ " && \n\
           \isabelle scalac $ISABELLE_SCALAC_OPTIONS " ^
              File.bash_paths (map (Path.append master_dir) sources) ^ " && \n\
           \isabelle_jdk jar cf " ^
              Bash.string (File.platform_path (Path.append master_dir target)) ^ " *");
    in if rc = 0 then writeln out else error out end);
\<close>

end
