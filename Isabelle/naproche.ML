(*
Authors: Makarius (2018)

Isabelle Prover IDE support for NaProChe / ForTheL.
*)

signature NAPROCHE =
sig
  val forthel_prove: bool Config.T
  val forthel_check: bool Config.T
  val forthel_skipfail: bool Config.T
  val process_forthel: Proof.context -> string * Position.T -> unit
end;

structure Naproche: NAPROCHE =
struct

(* options *)

val forthel_prove = Attrib.setup_option_bool (\<^system_option>\<open>forthel_prove\<close>, \<^here>);
val forthel_check = Attrib.setup_option_bool (\<^system_option>\<open>forthel_check\<close>, \<^here>);
val forthel_skipfail = Attrib.setup_option_bool (\<^system_option>\<open>forthel_skipfail\<close>, \<^here>);

fun bool_option ctxt config = if Config.get ctxt config then "on" else "off";


(* process ForTheL text *)

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

fun process_forthel ctxt (text, pos) =
  Isabelle_System.with_tmp_file "naproche" "ftl" (fn tmp_file =>
    let
      val pide =
        (case Position.get_id (Position.thread_data ()) of
          SOME id => id
        | NONE => raise Fail "Missing PIDE position id");

      val pos_file = the_default "" (Position.file_of pos);
      val pos_offset = the_default 0 (Position.offset_of pos);

      fun print_position props =
        let val pos = Position.of_properties props;
        in (case Position.here pos of "" => " " | s => s ^ "\n") end;

      fun output_acc acc =
        (case cat_lines (rev acc) of
          "" => ()
        | str =>
            (case try YXML.parse str of
              SOME (XML.Elem ((elem, props), body)) =>
                if elem = Markup.reportN then output_reports body
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

      val _ = File.write tmp_file text;
      val script =
        cat_lines [
          "set -e",
          "cd \"$NAPROCHE_HOME\"",
          "export PATH=\"$E_HOME:$SPASS_HOME:$PATH\"",
          "export NAPROCHE_PIDE=" ^ Bash.string pide,
          "export NAPROCHE_POS_FILE=" ^ Bash.string pos_file,
          "export NAPROCHE_POS_SHIFT=" ^ Bash.string (string_of_int (pos_offset - 1)),
          File.bash_path (Path.explode "$NAPROCHE_EXE") ^
            " --prove=" ^ bool_option ctxt forthel_prove ^
            " --check=" ^ bool_option ctxt forthel_check ^
            " --skipfail=" ^ bool_option ctxt forthel_skipfail ^
            " < " ^ File.bash_path tmp_file];
      val {out, err, rc, ...} = Bash.process script;
      val _ = detect_messages 0 [] (split_lines err);
      val _ = detect_messages 0 [] (split_lines out);
    in if rc = 0 then () else error ("Return code: " ^ string_of_int rc) end);

end;


(* Isabelle/Isar command setup *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>forthel\<close> "check Naproche-SAD text"
    (Parse.embedded_position >> (fn inp =>
      Toplevel.generic_theory (fn gthy =>
        (process_forthel (Context.proof_of gthy) inp; gthy))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>forthel_file\<close> "check Naproche-SAD text file (.ftl)"
    (Resources.provide_parse_files "forthel_file" >> (fn files =>
      Toplevel.generic_theory (fn gthy =>
        let
          val ([file], gthy') = Context.map_theory_result files gthy;
          val _ = process_forthel (Context.proof_of gthy) (cat_lines (#lines file), #pos file);
        in gthy' end)));

end;
