(*
Authors: Makarius (2018)

Support for SAD3 / ForTheL within Isabelle.
*)

theory SAD3
  imports Pure
  keywords "forthel_file" :: thy_load
begin

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

end
