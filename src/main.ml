
(* TabSat *)

open Options

(* Module inclusion for extensions to ensure they are linked *)
include Ext_eq
include Ext_meta
include Ext_prop
include Ext_logic
include Ext_arith
include Ext_prenex
include Ext_skolem
include Ext_functions

(* Exceptions *)
exception Sigint
exception Out_of_time
exception Out_of_space

(* GC alarm for time/space limits *)
let check size_limit = function () ->
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let s = float heap_size *. float Sys.word_size /. 8. in
  if s > size_limit then
    raise Out_of_space

let al = ref None
let setup_alarm t s = match !al with
  | None ->
    let _ = Unix.setitimer Unix.ITIMER_REAL
        Unix.{it_value = t; it_interval = 0.001 } in
    al := Some (Gc.create_alarm (check s))
  | Some _ -> assert false

let delete_alarm () = match !al with
  | Some alarm ->
    let _ = Unix.setitimer Unix.ITIMER_REAL
        Unix.{it_value = 0.; it_interval = 0. } in
    Gc.delete_alarm alarm;
    al := None
  | None -> ()

(* Model printing *)
let get_model () =
  List.sort (fun (t, _) (t', _) -> Expr.Term.compare t t')
     (Solver.full_model ())

(* Logging *)
let start_section l s =
  Util.debug l "=== %s %s" s (String.make (64 - String.length s) '=')

let end_section () = ()
(* Util.debug 1 "%s" (String.make 69 '=') *)

let wrap l s f x =
  start_section l s;
  let res = f x in
  end_section ();
  res

(* Level stack for push/pop operations *)
let level_stack = Stack.create ()

(* Execute given command *)
let do_command opt = function
  | Ast.Push ->
    wrap 0 "Push" (Stack.push (Solver.push ())) level_stack
  | Ast.Pop ->
    wrap 0 "Pop" Solver.pop (Stack.pop level_stack)
  | Ast.Cnf cnf ->
    if opt.solve then wrap 0 "assume" Solver.assume cnf
  | Ast.NewType (name, s, n) ->
    wrap 1 ("typing " ^ name) Type.new_type_def (s, n)
  | Ast.TypeDef (name, s, t) ->
    wrap 1 ("typing " ^ name) (Type.new_const_def (Io.input_env ())) (s, t)
  | Ast.Assert (name, t, goal) ->
    let f = wrap 1 ("typing " ^ name) (Type.parse ~goal (Io.input_env ())) t in
    if opt.solve then wrap 1 "assume" Solver.assume [[f]]
  | Ast.CheckSat ->
    if opt.solve then
      let res = wrap 0 "solve" Solver.solve () in
      Io.set_start ();
      begin match res with
        (* Model found *)
        | Solver.Sat ->
          Io.print_sat opt.out;
          (* Io.print_model opt.model_out (get_model ()); *)
          ()
        (* Proof found *)
        | Solver.Unsat ->
          Io.print_unsat opt.out;
          if opt.proof then begin
            let proof = Solver.get_proof () in
            Solver.print_dot_proof opt.dot_proof proof
          end
      end
  | c ->
    Io.print_error opt.out
      "%a : operation not supported yet" Ast.print_command_name c;
    exit 42

let rec do_commands opt commands =
  match wrap 1 "parsing" commands () with
  | None -> ()
  | Some c ->
    begin try
        if opt.interactive then
          setup_alarm opt.time_limit opt.size_limit;
        do_command opt c;
        if opt.interactive then
          delete_alarm ()
      with
      | Out_of_time ->
        delete_alarm ();
        Io.print_timeout Format.std_formatter
      | Type.Typing_error (msg, t) ->
        let loc = CCOpt.maybe CCFun.id (ParseLocation.mk opt.input_file 0 0 0 0) Ast.(t.loc) in
        Format.fprintf Format.std_formatter "While typing : %s@\n%a:@\n%s@."
          (Ast.s_term t) ParseLocation.fmt loc msg
    end;
    do_commands opt commands
  | exception Input.Lexing_error l ->
    Format.fprintf Format.std_formatter "%a@\n%a:@\nLexing error: invalid character@."
      ParseLocation.fmt_hint l ParseLocation.fmt l;
    do_commands opt commands
  | exception Input.Parsing_error (l, msg) ->
    Format.fprintf Format.std_formatter "%a@\n%a:@\n%s@."
      ParseLocation.fmt_hint l ParseLocation.fmt l msg;
    do_commands opt commands

(* Main function *)
let () =
  (* Argument parsing *)
  let man = Options.help_secs (Dispatcher.Plugin.ext_doc ()) (Semantics.Addon.ext_doc ()) in
  let info = Cmdliner.Term.(info ~sdocs:Options.copts_sect ~man ~version:"0.1" "tabsat") in
  let opts = Semantics.Addon.add_opts (Dispatcher.Plugin.add_opts (Options.copts_t ())) in
  let opt = match Cmdliner.Term.eval (opts, info) with
    | `Version | `Help -> exit 0
    | `Error `Parse | `Error `Term | `Error `Exn -> exit 1
    | `Ok opt -> opt
  in
  (* Gc alarm for limits *)
  if not opt.interactive then
    setup_alarm opt.time_limit opt.size_limit;

  (* Signal handlers *)
  Sys.set_signal Sys.sigint (Sys.Signal_handle (fun _ ->
      Util.need_cleanup := true;
      Util.debug 0 "Interrupted by user";
      raise Sigint));
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ ->
      Util.need_cleanup := true;
      Util.debug 0 "Alarm clock";
      raise Out_of_time));

  try
    (* Profiling *)
    if opt.profile.enabled then begin
      Util.enable_profiling ();
      Util.Section.set_profile_depth (CCOpt.get 0 opt.profile.max_depth);
      List.iter Util.Section.profile_section opt.profile.sections
    end;
    if opt.profile.print_stats then
      Util.enable_statistics ();

    (* Io options *)
    Io.set_input_file opt.input_file;
    Io.set_input opt.input_format;
    Io.set_output opt.output_format;

    (* Syntax extensions *)
    Semantics.Addon.set_exts "+base,+arith";
    List.iter Semantics.Addon.set_ext opt.addons;

    (* Extensions options *)
    Dispatcher.Plugin.set_exts "+eq,+uf,+logic,+prop,+skolem,+meta,+inst,+stats";
    List.iter Dispatcher.Plugin.set_ext opt.plugins;

    (* Print the current options *)
    wrap 0 "Options" (fun () ->
        Options.log_opts opt;
        Semantics.Addon.log_active 0;
        Dispatcher.Plugin.log_active 0) ();

    let commands = Io.parse_input opt.input_file in

    (* Commands execution *)
    do_commands opt commands;

    (* Output raw profiling data *)
    Util.csv_prof_data opt.profile.raw_data;

    (* Clean up *)
    Options.clean opt

  with
  | e ->
    let s = Printexc.get_backtrace () in
    let retcode = match e with
      | Out_of_time ->
        delete_alarm ();
        Io.print_timeout Format.std_formatter;
        0
      | Out_of_space ->
        delete_alarm ();
        Io.print_spaceout Format.std_formatter;
        0

      (* User interrupt *)
      | Sigint -> 1

      (* Parsing/Typing errors *)
      | Input.Lexing_error l ->
        Format.fprintf Format.std_formatter "%a:@\nLexing error: invalid character@." ParseLocation.fmt l;
        2
      | Input.Parsing_error (l, msg) ->
        Format.fprintf Format.std_formatter "%a:@\n%s@." ParseLocation.fmt l msg;
        2
      | Type.Typing_error (msg, t) ->
        let loc = CCOpt.maybe CCFun.id (ParseLocation.mk opt.input_file 0 0 0 0) Ast.(t.loc) in
        Format.fprintf Format.std_formatter "While typing : %s@\n%a:@\n%s@."
          (Ast.s_term t) ParseLocation.fmt loc msg;
        2

      (* Extension error *)
      | Extension.Abort (ext, reason) ->
        Format.fprintf Format.std_formatter "Extension '%s' aborted the proof search:@\n%s@." ext reason;
        (* No particuler exit code, because it most likely is the desired behavior *)
        0

      | Extension.Extension_not_found (sect, ext, l) ->
        Format.fprintf Format.std_formatter "Extension '%s/%s' not found. Available extensions are :@\n%a@."
          sect ext (fun fmt -> List.iter (fun s -> Format.fprintf fmt "%s " s)) l;
        3

      (* Internal errors. Should not happen *)
      | Dispatcher.Bad_assertion msg ->
        Format.fprintf Format.std_formatter "%s@." msg;
        4
      | Expr.Type_mismatch (t, ty1, ty2) ->
        Format.fprintf Format.std_formatter "Term %a has type %a but an expression of type %a was expected@."
          Expr.Print.term t Expr.Print.ty ty1 Expr.Print.ty ty2;
        4

      | _ ->
        Format.fprintf Format.std_formatter "Unexpected exception : %s@." (Printexc.to_string e);
        -1
    in
    if Printexc.backtrace_status () then
      Format.fprintf Format.std_formatter "%s" s;
    exit retcode

