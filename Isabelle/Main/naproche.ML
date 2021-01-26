(*
Authors: Makarius Wenzel (2018)

Isabelle Prover IDE support for NaProChe / ForTheL.
*)

signature NAPROCHE =
sig
  val naproche_server: bool Config.T
  val naproche_prove: bool Config.T
  val naproche_check: bool Config.T
  val naproche_skipfail: bool Config.T
  val naproche_print_thesis: bool Config.T
  val naproche_translate: bool Config.T
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
  val origin_translate: string
  val command_args: string
  val forthel_command: string
  val cancel_command: string
  val check_forthel: Proof.context -> {tex: bool} -> string * Position.T -> unit
end;

structure Naproche: NAPROCHE =
struct

(* options *)

val naproche_server = Attrib.setup_option_bool (\<^system_option>\<open>naproche_server\<close>, \<^here>);
val naproche_prove = Attrib.setup_option_bool (\<^system_option>\<open>naproche_prove\<close>, \<^here>);
val naproche_check = Attrib.setup_option_bool (\<^system_option>\<open>naproche_check\<close>, \<^here>);
val naproche_skipfail = Attrib.setup_option_bool (\<^system_option>\<open>naproche_skipfail\<close>, \<^here>);
val naproche_print_thesis = Attrib.setup_option_bool (\<^system_option>\<open>naproche_print_thesis\<close>, \<^here>);
val naproche_translate = Attrib.setup_option_bool (\<^system_option>\<open>naproche_translate\<close>, \<^here>);


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
val origin_translate = "Translation";


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

val command_args = "command_args";
val cancel_command = "cancel";
val forthel_command = "forthel";

fun check_forthel ctxt {tex} (text, pos) =
  let
    fun bool b = if b then "on" else "off";
    val bool_option = bool o Config.get ctxt;

    val (prover_server_port, prover_server_password) =
      if Options.default_bool \<^system_option>\<open>naproche_prover_server\<close> then
        (Options.default_string \<^system_option>\<open>naproche_prover_server_port\<close>,
         Options.default_string \<^system_option>\<open>naproche_prover_server_password\<close>)
      else ("", "");
    val args =
     ["--tex=" ^ bool tex,
      "--prove=" ^ bool_option naproche_prove,
      "--check=" ^ bool_option naproche_check,
      "--skipfail=" ^ bool_option naproche_skipfail,
      "--printthesis=" ^ bool_option naproche_print_thesis,
      "--translate=" ^ bool_option naproche_translate,
      "--prover-server-port=" ^ prover_server_port,
      "--prover-server-password=" ^ prover_server_password];

    val server_address = Options.default_string \<^system_option>\<open>naproche_server_address\<close>;
    val server_password = Options.default_string \<^system_option>\<open>naproche_server_password\<close>;
    fun server_connection f =
      server_address <> "" andalso server_password <> "" andalso
        server_address |> Socket_IO.with_streams (fn (in_stream, out_stream) =>
          let val _ = Byte_Message.write_line out_stream server_password in
            (case Byte_Message.read_line_message in_stream of
              NONE => false
            | SOME uuid => (f {in_stream = in_stream, out_stream = out_stream, uuid = uuid}; true))
          end);

    fun cancel_connection uuid =
      server_connection (fn {out_stream, ...} =>
        Byte_Message.write_line_message out_stream
          (YXML.string_of (XML.Elem ((cancel_command, []), XML.Encode.string uuid))));

    fun try_server () =
      server_connection (fn {in_stream, out_stream, uuid} =>
        let
          val props = (command_args, cat_lines args) :: naproche_environment pos;
          val _ =
            Byte_Message.write_line_message out_stream
              (YXML.string_of (XML.Elem ((forthel_command, props), XML.Encode.string text)));
        in input_messages in_stream end
        handle exn => (cancel_connection uuid; Exn.reraise exn))
      orelse (warning "Naproche-SAD server not active: using batch tool"; false);

    fun batch_tool () =
      Isabelle_System.with_tmp_file "naproche" "ftl" (fn tmp_file =>
        let
          val _ = File.write tmp_file text;
          val environment =
            naproche_environment pos
            |> map (fn (a, b) => "export " ^ a ^ "=" ^ Bash.string b);
          val script =
            cat_lines [
              "set -e",
              "cd \"$NAPROCHE_HOME\"",
              "export PATH=\"$E_HOME:$SPASS_HOME:$PATH\"",
              cat_lines environment,
              File.bash_path (Path.explode "$NAPROCHE_EXE") ^ " " ^ space_implode " " args ^
                " \"\" < " ^ File.bash_path tmp_file];
          val {out, err, rc, ...} = Bash.process script;
          val _ = read_messages err;
          val _ = read_messages out;
        in rc = 0 orelse error ("Return code: " ^ string_of_int rc) end);

    val _ = Config.get ctxt naproche_server andalso try_server () orelse batch_tool ();
  in () end;

end;


(* Isabelle/Isar command setup *)

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>forthel\<close> "check Naproche-SAD text"
    (Parse.embedded_position >> (fn inp => fn lthy => (check_forthel lthy {tex = false} inp; lthy)));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>forthel_tex\<close> "check Naproche-SAD text (TeX)"
    (Parse.embedded_position >> (fn inp => fn lthy => (check_forthel lthy {tex = true} inp; lthy)));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>forthel_file\<close> "check Naproche-SAD text file"
    (Resources.parse_file >> (fn get_file => fn lthy =>
        let
          val {src_path, lines, digest, pos} = get_file (Proof_Context.theory_of lthy);
          val file_name = Path.implode (Path.expand src_path);
          val tex = String.isSuffix ".ftl.tex" file_name;
          val lthy' = lthy
            |> Local_Theory.background_theory (Resources.provide (src_path, digest));
          val _ = check_forthel lthy' {tex = tex} (cat_lines lines, pos);
        in lthy' end));

end;
