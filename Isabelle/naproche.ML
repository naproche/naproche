(*
Authors: Makarius (2018)

Isabelle Prover IDE support for NaProChe / ForTheL.
*)

signature NAPROCHE =
sig
  val forthel_prove: bool Config.T
  val forthel_check: bool Config.T
  val forthel_skipfail: bool Config.T
  val forthel_file: Proof.context -> Token.file -> unit
end;

structure Naproche: NAPROCHE =
struct

(* options *)

val forthel_prove = Attrib.setup_option_bool (\<^system_option>\<open>forthel_prove\<close>, \<^here>);
val forthel_check = Attrib.setup_option_bool (\<^system_option>\<open>forthel_check\<close>, \<^here>);
val forthel_skipfail = Attrib.setup_option_bool (\<^system_option>\<open>forthel_skipfail\<close>, \<^here>);

fun bool_option ctxt config = if Config.get ctxt config then "on" else "off";


(* process ForTheL files *)

local

val output_reports = Output.report o map YXML.string_of;

val message_fns =
  Symtab.make
   [(Markup.stateN, Output.state),
    (Markup.writelnN, writeln),
    (Markup.informationN, Output.information),
    (Markup.tracingN, tracing),
    (Markup.warningN, warning),
    (Markup.legacyN, legacy_feature),
    (Markup.errorN, Output.error_message)]

fun output_message name =
  the_default writeln (Symtab.lookup message_fns name);

in

fun forthel_file ctxt (file: Token.file) =
  Isabelle_System.with_tmp_dir "naproche" (fn tmp_dir =>
    let
      val thy = Proof_Context.theory_of ctxt;

      val tmp_file = Path.append tmp_dir (Path.explode "input.ftl");
      val tmp_file_name = File.standard_path tmp_file;
      val _ = File.write tmp_file (cat_lines (#lines file));

      val pide_id =
        (case Position.get_id (Position.thread_data ()) of
          SOME id => id
        | NONE => raise Fail "Missing PIDE position id");

      val file_name =
        File.standard_path (Path.append (Resources.master_directory thy) (#src_path file));

      fun update_props props =
        let
          val props0 = Position.get_props (#pos file);
          val props1 =
            (case Properties.get props Markup.fileN of
              SOME name =>
                if name = tmp_file_name
                then Properties.put (Markup.fileN, file_name) props
                else props
            | NONE => props);
        in fold_rev Properties.put props1 props0 end;

      fun update_xml (XML.Elem ((elem, props), body)) = XML.Elem ((elem, update_props props), body)
        | update_xml xml = xml;

      fun print_position props =
        let val pos = Position.of_properties (update_props props);
        in (case Position.here pos of "" => " " | s => s ^ "\n") end;

      fun output_acc acc =
        (case cat_lines (rev acc) of
          "" => ()
        | str =>
            (case try YXML.parse str of
              SOME (XML.Elem ((elem, props), body)) =>
                if elem = Markup.reportN then output_reports (map update_xml body)
                else
                  output_message elem
                    (enclose "[" "]" (the_default "Naproche-SAD" (Properties.get props "origin")) ^
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
          "set -e",
          "cd \"$NAPROCHE_HOME\"",
          "export PATH=\"$E_HOME:$SPASS_HOME:$PATH\"",
          "export NAPROCHE_PIDE=" ^ Bash.string pide_id,
          File.bash_path (Path.explode "$NAPROCHE_EXE") ^
            " --prove=" ^ bool_option ctxt forthel_prove ^
            " --check=" ^ bool_option ctxt forthel_check ^
            " --skipfail=" ^ bool_option ctxt forthel_skipfail ^
            " -- " ^ File.bash_path tmp_file];
      val {out, err, rc, ...} = Bash.process script;
      val _ = detect_messages 0 [] (split_lines err);
      val _ = detect_messages 0 [] (split_lines out);
    in if rc = 0 then () else error ("Return code: " ^ string_of_int rc) end);

end;


(* Isabelle/Isar command setup *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>forthel_file\<close> "check NaProChe .ftl file"
    (Resources.provide_parse_files "forthel_file" >> (fn files =>
      Toplevel.generic_theory (fn gthy =>
        let
          val ([file], gthy') = Context.map_theory_result files gthy;
          val _ = forthel_file (Context.proof_of gthy) file;
        in gthy' end)));

end;
