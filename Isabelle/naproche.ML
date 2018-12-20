(*
Authors: Makarius (2018)

Isabelle Prover IDE support for NaProChe / ForTheL.
*)

signature NAPROCHE =
sig
  val forthel_prove: bool Config.T
  val forthel_check: bool Config.T
  val forthel_skipfail: bool Config.T
  val NAPROCHE_PIDE: string
  val NAPROCHE_POS_FILE: string
  val NAPROCHE_POS_SHIFT: string
  val origin: string
  val origin_main: string
  val origin_export: string
  val origin_forthel: string
  val origin_parser: string
  val origin_reasoner: string
  val origin_simplifier: string
  val origin_thesis: string
  val forthel_command: string
  val check_forthel: Proof.context -> string * Position.T -> unit
end;

structure Naproche: NAPROCHE =
struct

(* options *)

val forthel_prove = Attrib.setup_option_bool (\<^system_option>\<open>forthel_prove\<close>, \<^here>);
val forthel_check = Attrib.setup_option_bool (\<^system_option>\<open>forthel_check\<close>, \<^here>);
val forthel_skipfail = Attrib.setup_option_bool (\<^system_option>\<open>forthel_skipfail\<close>, \<^here>);

fun bool_option ctxt config = if Config.get ctxt config then "on" else "off";


(* environment *)

val NAPROCHE_PIDE = "NAPROCHE_PIDE";
val NAPROCHE_POS_FILE = "NAPROCHE_POS_FILE";
val NAPROCHE_POS_SHIFT = "NAPROCHE_POS_SHIFT";

fun naproche_environment pos =
  let
    val pide =
      (case Position.get_id (Position.thread_data ()) of
        SOME id => id
      | NONE => raise Fail "Missing PIDE position id");
    val pos_file = the_default "" (Position.file_of pos);
    val pos_offset = the_default 0 (Position.offset_of pos);
  in
    [(NAPROCHE_PIDE, pide),
     (NAPROCHE_POS_FILE, pos_file),
     (NAPROCHE_POS_SHIFT, string_of_int (pos_offset - 1))]
  end;


(* message origin *)

val origin = "origin";

val origin_main = "Main";
val origin_export = "Export";
val origin_forthel = "ForTheL";
val origin_parser = "Parser";
val origin_reasoner = "Reasoner";
val origin_simplifier = "Simplifier";
val origin_thesis = "Thesis";


(* process ForTheL text *)

local

val message_fns =
  Symtab.make
   [(Markup.stateN, Output.state),
    (Markup.writelnN, writeln),
    (Markup.informationN, Output.information),
    (Markup.tracingN, tracing),
    (Markup.warningN, warning),
    (Markup.legacyN, legacy_feature),
    (Markup.errorN, Output.error_message)]

fun output_message ((elem, props), body) =
  if elem = Markup.reportN then Output.report (map YXML.string_of body)
  else
    let
      val message_fn = the_default writeln (Symtab.lookup message_fns elem);
      val header = enclose "[" "]" (the_default origin_main (Properties.get props origin));
      val here = (case Position.here (Position.of_properties props) of "" => " " | s => s ^ "\n");
    in message_fn (header ^ here ^ YXML.string_of_body body) end;

fun input_messages in_stream =
  (case Byte_Message.read_line_message in_stream of
    NONE => ()
  | SOME msg =>
      (case try YXML.parse msg of
        SOME (XML.Text txt) => writeln txt
      | SOME (XML.Elem elem) => output_message elem
      | NONE => Output.error_message ("Malformed YXML tree " ^ quote msg);
      input_messages in_stream));

fun read_messages str =
  Isabelle_System.with_tmp_file "tmp" ""
    (fn path => (File.write path str; File.open_input input_messages path));

in

val forthel_command = "forthel";

fun check_forthel ctxt (text, pos) =
  let
    val server = Options.default_string \<^system_option>\<open>naproche_server\<close>;
    val password = Options.default_string \<^system_option>\<open>naproche_server_password\<close>;
    val prove = bool_option ctxt forthel_prove;
    val check = bool_option ctxt forthel_check;
    val skipfail = bool_option ctxt forthel_skipfail;
  in
    if server <> "" andalso password <> "" then
      server |> Socket_IO.with_streams (fn (in_stream, out_stream) =>
        let
          val _ = Byte_Message.write_line out_stream password;
          val props =
            naproche_environment pos @
              [(\<^system_option>\<open>forthel_prove\<close>, prove),
               (\<^system_option>\<open>forthel_check\<close>, check),
               (\<^system_option>\<open>forthel_skipfail\<close>, skipfail)];
          val _ =
            Byte_Message.write_line_message out_stream
              (YXML.string_of (XML.Elem ((forthel_command, props), XML.Encode.string text)));
          val _ = input_messages in_stream;
        in () end)
    else
      Isabelle_System.with_tmp_file "naproche" "ftl" (fn tmp_file =>
        let
          val _ = File.write tmp_file text;
          val environment =
            naproche_environment pos
            |> map (fn (a, b) => "export " ^ a ^ "=" ^ Bash.string b)
            |> cat_lines;
          val script =
            cat_lines [
              "set -e",
              "cd \"$NAPROCHE_HOME\"",
              "export PATH=\"$E_HOME:$SPASS_HOME:$PATH\"",
              environment,
              File.bash_path (Path.explode "$NAPROCHE_EXE") ^
                " --prove=" ^ prove ^ " --check=" ^ check ^ " --skipfail=" ^ skipfail ^
                " \"\" < " ^ File.bash_path tmp_file];
          val {out, err, rc, ...} = Bash.process script;
          val _ = read_messages err;
          val _ = read_messages out;
        in if rc = 0 then () else error ("Return code: " ^ string_of_int rc) end)
  end;

end;


(* Isabelle/Isar command setup *)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>forthel\<close> "check Naproche-SAD text"
    (Parse.embedded_position >> (fn inp => fn lthy => (check_forthel lthy inp; lthy)));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>forthel_file\<close> "check Naproche-SAD text file (.ftl)"
    (Resources.parse_files "forthel_file" >> (fn files => fn lthy =>
        let
          val [file] = files (Proof_Context.theory_of lthy);
          val lthy' = lthy
            |> Local_Theory.background_theory (Resources.provide (#src_path file, #digest file));
          val _ = check_forthel lthy' (cat_lines (#lines file), #pos file);
        in lthy' end));

end;
