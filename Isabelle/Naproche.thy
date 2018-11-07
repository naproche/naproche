(*
Authors: Makarius (2018)

Support for NaProChe / ForTheL within Isabelle.
*)

theory Naproche
  imports Pure Haskell.Haskell
  keywords "forthel_file" :: thy_load
begin


section \<open>Commands\<close>

ML_file "naproche.ML"

ML \<open>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>forthel_file\<close> "check NaProChe .ftl file"
    (Parse.token Parse.path >> (fn tok =>
      Toplevel.keep (fn st =>
        (case Token.get_files tok of
          [Exn.Res file] => Naproche.forthel_file (Toplevel.context_of st) file
        | _ => ()))));
\<close>


section \<open>Generated source modules\<close>

ML_command \<open>
  let
    val dir = Path.append (Resources.master_directory \<^theory>) \<^path>\<open>src/Isabelle\<close>
    val _ = Isabelle_System.mkdirs dir;
    val _ = Haskell.install_sources dir;
  in () end
\<close>

end
