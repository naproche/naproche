theory SAD3
  imports Pure
  keywords "forthel_file" :: thy_load
begin

ML \<open>
local

fun output_message "error" = Output.error_message
  | output_message "warning" = warning
  | output_message _ = writeln;

fun forthel_file ctxt (file: Token.file) =
  Isabelle_System.with_tmp_dir "SAD3" (fn tmp_dir =>
    let
      val thy = Proof_Context.theory_of ctxt;

      val tmp_file = Path.append tmp_dir (Path.explode "input.ftl");
      val tmp_file_name = File.standard_path tmp_file;
      val _ = File.write tmp_file (cat_lines (#lines file));

      val file_name =
        File.standard_path (Path.append (Resources.master_directory thy) (#src_path file));

      fun print_position props =
        let
          val pos =
            (case Properties.get props Markup.fileN of
              SOME name =>
                if name = tmp_file_name
                then Properties.put (Markup.fileN, file_name) props
                else props
            | NONE => props)
            |> Position.of_properties;
        in (case Position.here pos of "" => " " | s => s ^ "\n") end;

      fun output_acc acc =
        (case cat_lines (rev acc) of
          "" => ()
        | str =>
            (case try YXML.parse str of
              SOME (XML.Elem ((elem, props), body)) =>
                output_message elem
                  (enclose "[" "]" (the_default "SAD3" (Properties.get props "origin")) ^
                    print_position props ^ YXML.string_of_body body)
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

      val script =
        cat_lines [
          "cd \"$SAD3_HOME\"",
          "export PATH=\"$E_HOME:$SPASS_HOME:$PATH\"",
          "export SAD3_PIDE=true",
          "stack exec SAD3-exe -- --prove=off " ^ File.bash_path tmp_file];
      val (out, rc) = Isabelle_System.bash_output script;
      val _ = detect_messages 0 [] (split_lines out);
    in if rc = 0 then () else error ("Return code: " ^ string_of_int rc) end);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>forthel_file\<close> "check SAD3 .ftl file"
    (Parse.token Parse.path >> (fn tok =>
      Toplevel.keep (fn st =>
        (case Token.get_files tok of
          [Exn.Res file] => forthel_file (Toplevel.context_of st) file
        | _ => ()))));

in end;
\<close>

end
