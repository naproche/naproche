(*
Authors: Makarius Wenzel (2018)

Isabelle Prover IDE support for NaProChe / ForTheL.
*)

signature NAPROCHE =
sig
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
  val prover_args: string
  val uuid_command: string
  val forthel_command: string
  val cancel_command: string
  val check_forthel: Proof.context -> {tex: bool} -> string * Position.T -> unit
end;

structure Naproche: NAPROCHE =
struct

(* options *)

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

fun input_messages in_stream =
  let
    fun continue () = input_messages in_stream;
    fun skip info =
     (Output.system_message
        ("Ignoring bad server message" ^ (if info = "" then "" else " " ^ quote info));
      continue ());
  in
    (case Byte_Message.read_message in_stream of
      NONE => ()
    | SOME [] => skip ""
    | SOME (command :: args) =>
        if command = Markup.reportN then (Output.report args; continue ())
        else if Symtab.defined message_fns command andalso length args = 3 then
          let
            val message_fn = the (Symtab.lookup message_fns command);
            val [origin, position, text] = args;
            val header = enclose "[" "]" (if origin = "" then origin_main else origin);
            val props = XML.Decode.properties (YXML.parse_body position);
            val here =
              (case Position.here (Position.of_properties props) of "" => " " | s => s ^ "\n");
          in message_fn (header ^ here ^ text); continue () end
        else skip command)
  end

in

val prover_args = "prover_args";
val uuid_command = "uuid";
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

    fun server_error () =
      error ("Cannot connect to Naproche server " ^ quote server_address);

    fun server_connection body =
      if server_address = "" orelse server_password = "" then server_error ()
      else
        Socket_IO.with_streams'
          (fn (in_stream, out_stream) =>
            (case Byte_Message.read_message in_stream of
              SOME (command :: args) =>
                if command = uuid_command andalso length args = 1 then
                  body {in_stream = in_stream, out_stream = out_stream, uuid = nth args 0}
                else server_error ()
            | _ => server_error ()))
          server_address server_password;

    fun cancel_connection uuid =
      server_connection (fn {out_stream, ...} =>
        Byte_Message.write_message out_stream [cancel_command, uuid]);
  in
    server_connection (fn {in_stream, out_stream, uuid} =>
      let
        val opts = YXML.string_of_body (XML.Encode.properties (naproche_environment pos));
        val _ = Byte_Message.write_message out_stream [forthel_command, cat_lines args, opts, text]
      in input_messages in_stream end
      handle exn => (cancel_connection uuid; Exn.reraise exn))
  end;

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
