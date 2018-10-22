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
                [Exn.Res {lines, ...}] =>
                  Isabelle_System.with_tmp_dir "SAD3" (fn dir =>
                    let
                      val input_file = Path.append dir (Path.explode "input.ftl");
                      val _ = File.write input_file (cat_lines lines);
                      val script =
                        "cd \"$SAD3_HOME\"; stack exec SAD3-exe -- --PIDE=on --prove=off " ^  (* FIXME avoid "stack" *)
                        File.bash_path input_file;
                      val rc = Isabelle_System.bash script;
                    in if rc = 0 then () else error ("Return code: " ^ string_of_int rc) end)
              | _ => ());
          in () end)));
in end;
\<close>

end
