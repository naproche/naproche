(*
Authors: Makarius (2018)

Support for SAD3 / ForTheL within Isabelle.
*)

theory SAD3
  imports Pure Haskell.Haskell
  keywords "forthel_file" :: thy_load
begin


section \<open>Commands\<close>

ML_file "SAD3.ML"

ML \<open>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>forthel_file\<close> "check SAD3 .ftl file"
    (Parse.token Parse.path >> (fn tok =>
      Toplevel.keep (fn st =>
        (case Token.get_files tok of
          [Exn.Res file] => SAD3.forthel_file (Toplevel.context_of st) file
        | _ => ()))));
\<close>


section \<open>Generated source modules\<close>

ML_command \<open>
  let
    val dir = Path.append (Resources.master_directory \<^theory>) \<^path>\<open>src/Isabelle\<close>
    val _ = Isabelle_System.mkdirs dir;
  in
    Haskell.source_modules |> List.app (fn file => Isabelle_System.copy_file file dir)
  end
\<close>

end
