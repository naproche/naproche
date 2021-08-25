(*
Authors: Makarius Wenzel (2018, 2021)

Isabelle/Naproche connectivity, with Prover IDE support.
*)

signature NAPROCHE =
sig
  val naproche_prove: bool Config.T
  val naproche_check: bool Config.T
  val naproche_skipfail: bool Config.T
  val naproche_print_thesis: bool Config.T
  val naproche_translate: bool Config.T
  type state
  val get_theory: state -> generic_theory
  val map_theory_result: (generic_theory -> 'a * generic_theory) -> state -> 'a * state
  val map_theory: (generic_theory -> generic_theory) -> state -> state
  val theory_of_state: state -> theory
  val context_of_state: state -> Proof.context
  type command = string list * state -> string list * state
  type command0 = string list -> unit
  val command_setup: binding -> command -> theory -> theory
  val command0_setup: binding -> command0 -> theory -> theory
  val cancel_program: string
  val forthel_program: string
  val check_forthel: Proof.context -> {tex: bool} -> string * Position.T -> unit
end;

structure Naproche: NAPROCHE =
struct

(** options **)

val naproche_prove = Attrib.setup_option_bool (\<^system_option>\<open>naproche_prove\<close>, \<^here>);
val naproche_check = Attrib.setup_option_bool (\<^system_option>\<open>naproche_check\<close>, \<^here>);
val naproche_skipfail = Attrib.setup_option_bool (\<^system_option>\<open>naproche_skipfail\<close>, \<^here>);
val naproche_print_thesis = Attrib.setup_option_bool (\<^system_option>\<open>naproche_print_thesis\<close>, \<^here>);
val naproche_translate = Attrib.setup_option_bool (\<^system_option>\<open>naproche_translate\<close>, \<^here>);

fun naproche_options pos =
  let
    val pos_id =
      (case Position.id_of (Position.thread_data ()) of
        SOME id => id
      | NONE => raise Fail "Missing PIDE position id");
    val pos_file = the_default "" (Position.file_of pos);
    val pos_offset = the_default 0 (Position.offset_of pos);
  in
    Options.default ()
    |> Options.put_string \<^system_option>\<open>naproche_pos_id\<close> pos_id
    |> Options.put_string \<^system_option>\<open>naproche_pos_file\<close> pos_file
    |> Options.put_int \<^system_option>\<open>naproche_pos_shift\<close> (pos_offset - 1)
  end;



(** commands in ML **)

(* state *)

datatype state = State of {threads: string list, theory: generic_theory};

fun make_state (threads, theory) = State {threads = threads, theory = theory};
fun map_state f (State {threads, theory}) = make_state (f (threads, theory));

fun get_threads (State ({threads, ...})) = threads;
fun get_theory (State ({theory, ...})) = theory;

val map_threads = map_state o @{apply 2(1)};

fun map_theory_result f state =
  let
    val (res, theory') = f (get_theory state);
    val state' = map_state (fn (threads, _) => (threads, theory')) state;
  in (res, state') end;

fun map_theory f = map_theory_result (f #> pair ()) #> #2;

val theory_of_state = Context.theory_of o get_theory;
val context_of_state = Context.proof_of o get_theory;


(* commands *)

type command = string list * state -> string list * state;
type command0 = string list -> unit

structure Data = Theory_Data
(
  type T = command Name_Space.table;
  val empty : T = Name_Space.empty_table "naproche_command";
  val extend = I;
  fun merge data : T = Name_Space.merge_tables data;
);

fun command_setup binding cmd thy =
  thy |> Data.put (#2 (Name_Space.define (Context.Theory thy) true (binding, cmd) (Data.get thy)));

fun command0_setup binding (cmd: command0) =
  command_setup binding (fn (args, state) => (cmd args; ([], state)));

val get_command = Name_Space.lookup o Data.get;

fun check_command thy = #1 o Name_Space.check (Context.Theory thy) (Data.get thy);

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>naproche_command\<close>
   (Args.theory -- Scan.lift Args.embedded_position >>
     (ML_Syntax.print_string o uncurry check_command)));



(** programs in Haskell **)

(* server connection *)

fun read_message streams = Byte_Message.read_message (fst streams);
fun write_message streams = Byte_Message.write_message (snd streams);

fun with_server f =
  let
    val server_address = Options.default_string \<^system_option>\<open>naproche_server_address\<close>;
    val server_password = Options.default_string \<^system_option>\<open>naproche_server_password\<close>;
  in
    if server_address = "" orelse server_password = ""
    then error "Nissing Isabelle/Naproche server"
    else Socket_IO.with_streams' f server_address server_password
  end;


(* threads in Haskell *)

val cancel_program = "cancel";

fun cancel state =
  with_server (fn streams => write_message streams (cancel_program :: get_threads state));

val _ = Theory.setup
 (command_setup \<^binding>\<open>threads\<close> (fn (more_threads, state) =>
   ([], map_threads (fold (insert op =) more_threads) state)));


(* command loop *)

fun command_loop streams state =
  (case read_message streams of
    NONE => ()
  | SOME [] => command_loop streams state
  | SOME (name :: args) =>
      (case get_command (theory_of_state state) name of
        NONE => raise Fail ("Protocol error: bad Isabelle/Naproche command " ^ quote name)
      | SOME cmd =>
          (case Exn.interruptible_capture cmd (args, state) of
            Exn.Exn exn =>
              raise Fail ("Protocol error: failure of Isabelle/Naproche command " ^ quote name
                ^ "\n" ^ Runtime.exn_message exn)
          | Exn.Res (result, state') =>
              (write_message streams result; command_loop streams state'))))
  handle exn => (cancel state; Exn.reraise exn);


(* process ForTheL text *)

val forthel_program = "forthel";

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

    val opts = YXML.string_of_body (Options.encode (naproche_options pos));

    val state = make_state ([], Context.Theory (Proof_Context.theory_of ctxt));
  in
    with_server (fn streams =>
     (write_message streams [forthel_program, cat_lines args, opts, text];
      command_loop streams state))
  end;


(* output messages *)

val _ = Theory.setup
 (command0_setup \<^binding>\<open>output_state\<close> (Output.state o the_single) #>
  command0_setup \<^binding>\<open>output_writeln\<close> (writeln o the_single) #>
  command0_setup \<^binding>\<open>output_information\<close> (Output.information o the_single) #>
  command0_setup \<^binding>\<open>output_tracing\<close> (tracing o the_single) #>
  command0_setup \<^binding>\<open>output_warning\<close> (warning o the_single) #>
  command0_setup \<^binding>\<open>output_legacy_feature\<close> (legacy_feature o the_single) #>
  command0_setup \<^binding>\<open>output_error\<close> (Output.error_message o the_single) #>
  command0_setup \<^binding>\<open>output_report\<close> Output.report);


(* serial numbers from Isabelle/ML *)

val _ = Theory.setup
  (command_setup \<^binding>\<open>serials\<close>
    (apfst (fn [n] => replicate (Value.parse_nat n) () |> map serial_string)));



(** Isabelle/Isar commands **)

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
