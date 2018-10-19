theory SAD3
  imports Pure
  keywords "forthel_file" :: thy_load
begin

ML \<open>
local
  val _ =
    Outer_Syntax.command \<^command_keyword>\<open>forthel_file\<close> "check SAD3 .ftl file"
      (Scan.ahead Parse.not_eof -- Parse.position Parse.path >> (fn (tok, path) =>
        Toplevel.keep (fn st =>
          let
            val ctxt = Toplevel.context_of st;
            val thy = Toplevel.theory_of st;
            val _ = Resources.check_path ctxt (Resources.master_directory thy) path;
            val _ =
              (case Token.get_files tok of
                [Exn.Res {lines, pos, ...}] => ()  (* FIXME *)
              | _ => ());
          in () end)));
in end;
\<close>

end
