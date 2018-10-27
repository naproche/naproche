theory SAD3
  imports Pure
  keywords "forthel_file" :: thy_load
begin

ML \<open>
local
  fun message_fn "error" = Output.error_message
    | message_fn "warning" = warning
    | message_fn _ = writeln;

  fun output_acc acc =
    (case cat_lines (rev acc) of
      "" => ()
    | str =>
        (case try YXML.parse str of
          SOME (XML.Elem ((elem, props), body)) =>
            message_fn elem
              (enclose "[" "]" (the_default "SAD3" (Properties.get props "origin")) ^
              (case Position.here (Position.of_properties props) of
                "" => " "
              | s => s ^ "\n") ^ YXML.string_of_body body)
        | SOME (XML.Text s) => writeln s
        | NONE => Output.error_message ("Malformed YXML tree " ^ quote str)));

  fun detect_messages 0 acc (line :: lines) =
        (output_acc acc;
         case line |> try (unprefix "\001") |> Option.mapPartial (try Value.parse_nat) of
          SOME n => detect_messages n [] lines
        | NONE => (writeln line; detect_messages 0 [] lines))
    | detect_messages n acc [line] = detect_messages (n - size line) (line :: acc) []
    | detect_messages n acc (line :: lines) =
        let val n' = n - size line
        in detect_messages (if n' > 0 then n' - 1 else n') (line :: acc) lines end
    | detect_messages n acc [] =
        (output_acc acc;
         if n = 0 then ()
         else Output.error_message ("Illegal remaining bytes " ^ signed_string_of_int n));

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
                        cat_lines [
                          "cd \"$SAD3_HOME\"",
                          "export PATH=\"$E_HOME:$SPASS_HOME:$PATH\"",
                          "export SAD3_PIDE=true",
                          "stack exec SAD3-exe -- --prove=off " ^ File.bash_path input_file]; (* FIXME avoid "stack" *)
                      val (out, rc) = Isabelle_System.bash_output script;
                      val _ = detect_messages 0 [] (split_lines out);
                    in if rc = 0 then () else error ("Return code: " ^ string_of_int rc) end)
              | _ => ());
          in () end)));
in end;
\<close>

end
