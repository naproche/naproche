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
  val naproche_translation: bool Config.T
  val naproche_isabelle: bool Config.T
  type state
  val get_theory: state -> theory
  val get_context: state -> Proof.context
  val map_theory_result: (theory -> 'a * theory) -> state -> 'a * state
  val map_theory: (theory -> theory) -> state -> state
  type command = string list * state -> string list * state
  type command0 = string list -> unit
  val command_setup: binding -> command -> theory -> theory
  val command0_setup: binding -> command0 -> theory -> theory
  val command1_setup: binding -> (Proof.context -> string -> string) -> theory -> theory
  val yxml_command1_setup: binding -> (Proof.context -> XML.body -> XML.body) -> theory -> theory
  val cancel_program: string
  val forthel_program: string
  val check_forthel: {tex: bool} -> string * Position.T -> theory -> theory
  type sequent = term list * term list
  val prove_sequent: binding -> sequent -> Input.source -> Proof.context -> thm list * Proof.context
  val present_sequent: sequent -> Proof.context ->
    {fixes: Element.context_i list,
     assumes: Element.context_i list,
     shows: Element.statement_i} * Proof.context
  val pretty_sequent: Proof.context -> sequent -> Pretty.T
  val string_of_sequent: Proof.context -> sequent -> string
  type problem = {sequent: sequent, fact: thm list option}
  val problem_space: theory -> Name_Space.T
  val get_problem: theory -> string -> problem option
  val check_problem: Proof.context -> xstring * Position.T -> string
  val define_problem: binding -> sequent -> theory -> string * theory
  val state_problem: xstring * Position.T -> bool -> local_theory -> Proof.state
  val pretty_problems: Proof.context -> Pretty.T list
end;

structure Naproche: NAPROCHE =
struct

(** options **)

val naproche_prove = Attrib.setup_option_bool (\<^system_option>\<open>naproche_prove\<close>, \<^here>);
val naproche_check = Attrib.setup_option_bool (\<^system_option>\<open>naproche_check\<close>, \<^here>);
val naproche_skipfail = Attrib.setup_option_bool (\<^system_option>\<open>naproche_skipfail\<close>, \<^here>);
val naproche_print_thesis = Attrib.setup_option_bool (\<^system_option>\<open>naproche_print_thesis\<close>, \<^here>);
val naproche_translation = Attrib.setup_option_bool (\<^system_option>\<open>naproche_translation\<close>, \<^here>);
val naproche_isabelle = Attrib.setup_option_bool (\<^system_option>\<open>naproche_isabelle\<close>, \<^here>);

fun naproche_options ctxt pos =
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
    |> Options.put_bool \<^system_option>\<open>naproche_isabelle\<close> (Config.get ctxt naproche_isabelle)
  end;



(** commands in ML **)

(* state *)

datatype state = State of {threads: string list, theory: theory};

fun make_state (threads, theory) = State {threads = threads, theory = theory};
fun map_state f (State {threads, theory}) = make_state (f (threads, theory));

fun get_threads (State ({threads, ...})) = threads;
fun get_theory (State ({theory, ...})) = theory;

val get_context = Proof_Context.init_global o get_theory;

val map_threads = map_state o @{apply 2(1)};

fun map_theory_result f state =
  let
    val (res, theory') = f (get_theory state);
    val state' = map_state (fn (threads, _) => (threads, theory')) state;
  in (res, state') end;

fun map_theory f = map_theory_result (f #> pair ()) #> #2;


(* commands *)

type command = string list * state -> string list * state;
type command0 = string list -> unit

local

structure Data = Theory_Data
(
  type T = command Name_Space.table;
  val empty : T = Name_Space.empty_table "naproche_command";
  fun merge data : T = Name_Space.merge_tables data;
);

in

fun command_setup binding cmd thy =
  thy |> Data.map (#2 o Name_Space.define (Context.Theory thy) true (binding, cmd));

fun command0_setup binding (cmd: command0) =
  command_setup binding (fn (args, state) => (cmd args; ([], state)));

fun command1_setup binding cmd =
  command_setup binding (fn (args, state) => (map (cmd (get_context state)) args, state));

fun yxml_command1_setup binding cmd =
  command1_setup binding (fn ctxt => YXML.parse_body #> cmd ctxt #> YXML.string_of_body);

val get_command = Name_Space.lookup o Data.get;

fun check_command thy = #1 o Name_Space.check (Context.Theory thy) (Data.get thy);

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>naproche_command\<close>
   (Args.theory -- Scan.lift Parse.embedded_position >>
     (ML_Syntax.print_string o uncurry check_command)));

end;



(** programs in Haskell **)

(* server connection *)

fun read_message streams =
  Byte_Message.read_message (fst streams) |> (Option.map o map) Bytes.content;

fun write_message streams =
  map Bytes.string #> Byte_Message.write_message (snd streams);

fun with_server f =
  let
    val server_address = Options.default_string \<^system_option>\<open>naproche_server_address\<close>;
    val server_password = Options.default_string \<^system_option>\<open>naproche_server_password\<close>;
  in
    if server_address = "" orelse server_password = ""
    then error "Missing Isabelle/Naproche server"
    else Socket_IO.with_streams' f server_address server_password
  end;


(* threads in Haskell *)

val cancel_program = "cancel";

fun cancel state =
  with_server (fn streams =>
    write_message streams (cancel_program :: get_threads state));

val _ = Theory.setup
 (command_setup \<^binding>\<open>threads\<close> (fn (more_threads, state) =>
   ([], map_threads (fold (insert op =) more_threads) state)));


(* command loop *)

fun command_loop streams state =
  (case Exn.capture read_message streams of
    Exn.Res NONE => state
  | Exn.Res (SOME []) => command_loop streams state
  | Exn.Res (SOME (name :: args)) =>
      (case get_command (get_theory state) name of
        NONE => raise Fail ("Protocol error: bad Isabelle/Naproche command " ^ quote name)
      | SOME cmd =>
          (case Exn.result cmd (args, state) of
            Exn.Exn exn =>
              raise Fail ("Protocol error: failure of Isabelle/Naproche command " ^ quote name ^
                "\n" ^ Runtime.exn_message (Runtime.exn_context (SOME (get_context state)) exn))
          | Exn.Res (result, state') =>
              (write_message streams result; command_loop streams state')))
  | Exn.Exn exn => (cancel state; Exn.reraise exn));


(* process ForTheL text *)

val forthel_program = "forthel";

fun forthel_bool b = if b then "on" else "off";
fun forthel_bool_option ctxt = forthel_bool o Config.get ctxt;

fun forthel_args ctxt {tex} =
  let val bool_option = forthel_bool_option ctxt in
   ["--tex=" ^ forthel_bool tex,
    "--prove=" ^ bool_option naproche_prove,
    "--check=" ^ bool_option naproche_check,
    "--skipfail=" ^ bool_option naproche_skipfail,
    "--printthesis=" ^ bool_option naproche_print_thesis,
    "--translation=" ^ bool_option naproche_translation]
  end;

fun check_forthel tex (text, pos) thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val args = forthel_args ctxt tex;
    val opts = YXML.string_of_body (Options.encode (naproche_options ctxt pos));
  in
    with_server (fn streams =>
     (write_message streams [forthel_program, cat_lines args, opts, text];
      command_loop streams (make_state ([], thy))))
    |> get_theory
  end;



(** Naproche logic within Isabelle **)

(* sequents *)

type sequent = term list * term list;

fun declare_sequent (sequent: sequent) ctxt =
  let
    val ts = op @ sequent;
    val xs = rev (fold (Variable.add_frees ctxt) ts []);
    val ctxt' = fold Variable.add_fixes_implicit ts ctxt;
  in (xs, ctxt') end;

fun make_fixes xs = xs |> map (fn (x, T: typ) => (Binding.name x, SOME T, NoSyn));
fun make_assumes assms = assms |> map (fn t: term => (Binding.empty_atts, [(t, []: term list)]));
fun make_shows concls = [(Binding.empty_atts, map (rpair ([]: term list)) concls)];

fun have_sequent (asms, concls) =
  Context_Position.set_visible false
  #> Proof.init
  #> Proof.begin_block
  #> Proof.have false NONE (K I) [] (make_assumes asms) (make_shows concls) false #> #2;

fun prove_sequent binding sequent method ctxt =
  let
    val state1 = ctxt |> declare_sequent sequent |> #2 |> have_sequent sequent;
    val text = #1 (Method.read_closure_input (Proof.context_of state1) method);
    val state2 = state1 |> Proof.local_terminal_proof ((text, Position.no_range), NONE);
    val res = Proof_Context.export (Proof.context_of state2) ctxt (Proof.the_facts state2);
  in ctxt |> Proof_Context.note_thms "" ((binding, []), [(res, [])]) |>> #2 end;

fun present_sequent ((assms, concls): sequent) ctxt =
  let
    val (xs, ctxt') = declare_sequent (assms, concls) ctxt;
    val fixes = if null xs then [] else [Element.Fixes (make_fixes xs)];
    val assumes = if null assms then [] else [Element.Assumes (make_assumes assms)];
    val shows = Element.Shows (make_shows concls);
  in ({fixes = fixes, assumes = assumes, shows = shows}, ctxt') end;

fun check_sequent ctxt sequent =
  (List.app (ignore o Proof_Context.cert_prop ctxt) (op @ sequent); sequent);

fun pretty_sequent ctxt sequent =
  let
    val ({fixes, assumes, shows}, ctxt') = present_sequent (check_sequent ctxt sequent) ctxt;
  in
    maps (Element.pretty_ctxt ctxt') (fixes @ assumes) @ Element.pretty_stmt ctxt' shows
  end |> Pretty.chunks;

val string_of_sequent = Pretty.string_of oo pretty_sequent;


(* proof problems *)

type problem = {sequent: sequent, fact: thm list option};

local

structure Data = Theory_Data
(
  type T = problem Name_Space.table * int;
  val empty : T = (Name_Space.empty_table "naproche_problem", 0);
  fun merge ((table1, _), (table2, _)) : T = (Name_Space.merge_tables (table1, table2), 0);
);

in

val problem_table = #1 o Data.get;
val problem_space = problem_table #> Name_Space.space_of_table;

val get_problem = problem_table #> Name_Space.lookup;

fun check_problem ctxt =
  #1 o Name_Space.check (Context.Proof ctxt) (problem_table (Proof_Context.theory_of ctxt));

fun print_problem ctxt name =
  let
    val thy = Proof_Context.theory_of ctxt;
    val (markup, xname) = Name_Space.markup_extern ctxt (problem_space thy) name;
  in Markup.markup markup xname end;

fun define_problem binding sequent thy =
  let
    val ctxt = Proof_Context.init_global thy;

    val (table, index) = Data.get thy;
    val index' = index + 1;
    val n = string_of_int index';
    val binding' = binding |> Binding.map_name
      (fn "" => n | a => Symbol.explode a |> map (fn "\<index>" => n | s => s) |> implode);
    val problem = {sequent = check_sequent ctxt sequent, fact = NONE};
    val (name, table') = Name_Space.define (Context.Theory thy) true (binding', problem) table;
  in (name, Data.put (table', index') thy) end;

fun solve_problem name fact =
  (Data.map o apfst o Name_Space.map_table_entry name)
    (fn {sequent, ...} => {sequent = sequent, fact = SOME fact});

end;

fun state_problem (xname, pos) int lthy =
  let
    val _ = Local_Theory.assert lthy;
    val thy = Proof_Context.theory_of lthy;

    val name = check_problem lthy (xname, pos);
    fun err msg = error (msg ^ quote (print_problem lthy name) ^ Position.here pos);
    val sequent =
      (case get_problem thy name of
        NONE => err "Bad problem"
      | SOME {fact = SOME _, ...} => err "Problem already solved"
      | SOME {sequent, ...} => sequent);

    fun after_qed results lthy' =
      let val fact = Proof_Context.export lthy' (Proof_Context.init_global thy) (flat results);
      in Local_Theory.background_theory (solve_problem name fact) lthy' end;
    val binding = Binding.make (Long_Name.base_name name, pos);
    val ({fixes, assumes, shows}, _) = present_sequent sequent lthy;
  in
    Specification.theorem true "" NONE after_qed (binding, []) [] (fixes @ assumes) shows int lthy
  end;

fun pretty_problems ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val space = problem_space thy;
    val (solved, unsolved) =
      Name_Space.extern_table true ctxt (problem_table thy)
      |> sort (Name_Space.entry_ord space o apply2 (#1 o #1))
      |> List.partition (is_some o #fact o #2);
    fun pretty ((name, xname), problem) =
      Pretty.item
       [Pretty.mark_str (Name_Space.markup space name, xname), Pretty.str ":", Pretty.fbrk,
        pretty_sequent ctxt (#sequent problem)];
    fun pretty_list head list =
      if null list then []
      else [Pretty.big_list (head ^ " (" ^ string_of_int (length list) ^ "):") (map pretty list)];
  in pretty_list "solved" solved @ pretty_list "unsolved" unsolved end;



(** Isabelle/Naproche protocol commands **)

fun cert_term ctxt t =
  let
    val t' = Proof_Context.cert_term ctxt t;
    val T = Term.type_of t';
  in (t', T) end;

val decode_term = Term_XML.Decode.term o Proof_Context.consts_of;
val encode_term = Term_XML.Encode.term o Proof_Context.consts_of;

fun decode_sequent ctxt =
  let val decode = XML.Decode.list (decode_term ctxt)
  in XML.Decode.pair decode decode end;

val _ = Theory.setup
 (command_setup \<^binding>\<open>serials\<close>
    (apfst (fn [n] => replicate (Value.parse_nat n) () |> map serial_string)) #>
  yxml_command1_setup \<^binding>\<open>cert_terms\<close>
    (fn ctxt =>
      decode_term ctxt #> cert_term ctxt #>
      XML.Encode.pair (encode_term ctxt) Term_XML.Encode.typ) #>
  yxml_command1_setup \<^binding>\<open>print_terms\<close>
    (fn ctxt => decode_term ctxt #> Syntax.string_of_term ctxt #> XML.Encode.string) #>
  yxml_command1_setup \<^binding>\<open>print_sequents\<close>
    (fn ctxt => decode_sequent ctxt #> string_of_sequent ctxt #> XML.Encode.string) #>
  command_setup \<^binding>\<open>define_problems\<close>
    (fn (args, state) =>
      let
        val ctxt = get_context state;
        fun define arg =
          let
            val (bname, pos, sequent) = YXML.parse_body arg |>
              let open XML.Decode
              in triple string (Position.of_properties o properties) (decode_sequent ctxt) end;
          in define_problem (Binding.make (bname, pos)) sequent end;
      in fold_map (map_theory_result o define) args state end) #>
  command0_setup \<^binding>\<open>output_report\<close> Output.report #>
  command0_setup \<^binding>\<open>output_state\<close> (Output.state o the_single) #>
  command0_setup \<^binding>\<open>output_writeln\<close> (writeln o the_single) #>
  command0_setup \<^binding>\<open>output_information\<close> (Output.information o the_single) #>
  command0_setup \<^binding>\<open>output_tracing\<close> (tracing o the_single) #>
  command0_setup \<^binding>\<open>output_warning\<close> (warning o the_single) #>
  command0_setup \<^binding>\<open>output_legacy_feature\<close> (legacy_feature o the_single) #>
  command0_setup \<^binding>\<open>output_error\<close> (Output.error_message o the_single));



(** Isabelle/Isar commands **)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>forthel\<close> "check Naproche text"
    (Parse.embedded_position >> (Toplevel.theory o check_forthel {tex = false}));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>forthel_tex\<close> "check Naproche text (TeX)"
    (Parse.embedded_position >> (Toplevel.theory o check_forthel {tex = true}));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>forthel_file\<close> "check Naproche text file"
    (Resources.provide_parse_file >> (fn get_file =>
      Toplevel.theory (fn thy =>
        let
          val ({src_path, lines, pos, ...}, thy') = get_file thy;
          val file_name = Path.implode (Path.expand src_path);
          val tex = String.isSuffix ".ftl.tex" file_name;
        in check_forthel {tex = tex} (cat_lines lines, pos) thy' end)));

val _ =
  Outer_Syntax.local_theory_to_proof' \<^command_keyword>\<open>naproche_problem\<close> "prove Naproche problem"
    (Parse.name_position >> state_problem);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>naproche_problems\<close> "print Naproche problems"
    (Scan.succeed (Toplevel.keep (fn st =>
      Pretty.writeln (Pretty.chunks (pretty_problems (Toplevel.context_of st))))));

end;
