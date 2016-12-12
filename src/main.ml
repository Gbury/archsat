
(* ArchSat *)

open Options

module T = Dolmen.Term
module S = Dolmen.Statement

(* Module inclusion for extensions to ensure they are linked *)
include Ext_eq
include Ext_meta
include Ext_prop
include Ext_logic
include Ext_arith
include Ext_prenex
include Ext_skolem
include Ext_functions
include Ext_constraints

(* Exceptions *)

(* Logging *)
let start_section l s =
  Util.debug l "=== %s %s" s (String.make (64 - String.length s) '=')

(* Prelude strings for interactive mode. *)
let prelude_strings opt =
  match opt.input_format with
  | None -> "", ""
  | Some l ->
    let s = Format.asprintf "(%s)# @?" (In.string_of_language l) in
    s, String.make (String.length s) ' '

(* Execute given command *)
let rec do_command opt = function

  (* Pack of commands *)
  | { S.descr = S.Pack l } ->
    do_commands opt (Gen.of_list l)

  (* Declarations and definitions *)
  | { S.descr = S.Decl (id, t) } ->
    start_section 0 "Declaration";
    let l = CCOpt.get_exn opt.input_format in
    let env = Type.empty_env ~status:Expr.Status.hypothesis (Semantics.type_env l) in
    Type.new_decl env t id
  | { S.descr = S.Def (id, t) } ->
    start_section 0 "Definition";
    let l = CCOpt.get_exn opt.input_format in
    let env = Type.empty_env ~status:Expr.Status.hypothesis (Semantics.type_env l) in
    Type.new_def env t id

  (* New assertions *)
  | { S.descr = S.Antecedent t } ->
    start_section 0 "Typing";
    let l = CCOpt.get_exn opt.input_format in
    let env = Type.empty_env ~status:Expr.Status.hypothesis (Semantics.type_env l) in
    let f = Type.new_formula env t in
    start_section 0 "Assume";
    Solver.assume [[f]]
  | { S.descr = S.Consequent t } ->
    start_section 0 "Typing";
    let l = CCOpt.get_exn opt.input_format in
    let env = Type.empty_env ~status:Expr.Status.goal (Semantics.type_env l) in
    let f = Type.new_formula env t in
    start_section 0 "Assume";
    Solver.assume [[Expr.Formula.neg f]]

  (* Time to solve ! *)
  | { S.descr = S.Prove } ->
    if opt.solve then begin
      Out.set_start ();
      start_section 0 "Solve";
      begin match Solver.solve () with
        (* Model found *)
        | Solver.Sat _ ->
          Out.print_sat opt.out;
          (* Io.print_model opt.model_out (get_model ()); *)
          ()
        (* Proof found *)
        | Solver.Unsat proof ->
          Out.print_unsat opt.out
        (* No concrete result *)
        | Solver.Unknown ->
          Out.print_unknown opt.out
      end
    end

  (* Exit *)
  | { S.descr = S.Exit } ->
    raise (Exit 0)

  | c ->
    Util.debug 0
      "The following command is not yet understood: %a"
      Dolmen.Statement.pp c

and do_commands opt commands =
  let prelude, pre_space = prelude_strings opt in
  if opt.interactive then
    Format.printf "%s@?" prelude;
  begin match commands () with
    | None -> ()
    | Some c ->
      begin
        try
          if opt.interactive then
            setup_alarm opt.time_limit opt.size_limit;
          do_command opt c;
          if opt.interactive then
            delete_alarm ();
          ()
        with
        | Out_of_time ->
          delete_alarm ();
          Out.print_timeout Format.std_formatter;
          if not opt.interactive then raise (Exit 0)
        | Out_of_space ->
          delete_alarm ();
          Out.print_spaceout Format.std_formatter;
          if not opt.interactive then raise (Exit 0)
        | Type.Typing_error (msg, t) ->
          delete_alarm ();
          let loc = CCOpt.maybe CCFun.id
              (Dolmen.ParseLocation.mk (input_to_string opt.input_file) 0 0 0 0) T.(t.loc)
          in
          Format.fprintf Format.std_formatter "While typing %a@\n" T.print t;
          Format.fprintf Format.std_formatter "%a:@\n%s@." Dolmen.ParseLocation.fmt loc msg;
          if not opt.interactive then raise (Exit 2)
        | Extension.Abort (ext, reason) ->
          Format.fprintf Format.std_formatter "Extension '%s' aborted the proof search:@\n%s@." ext reason;
          if not opt.interactive then raise (Exit 0)
      end;
      do_commands opt commands
    | exception Dolmen.ParseLocation.Lexing_error (loc, msg) ->
      if opt.interactive then
        Format.fprintf Format.std_formatter "%s%a@\n"
          (if Dolmen.ParseLocation.(loc.start_line = 1) then pre_space else "")
          Dolmen.ParseLocation.fmt_hint loc;
      Format.fprintf Format.std_formatter "%a:@\n%s@."
        Dolmen.ParseLocation.fmt loc (match msg with | "" -> "Lexing error: invalid character" | x -> x);
      if opt.interactive then
        do_commands opt commands
      else
        raise (Exit 1)
    | exception Dolmen.ParseLocation.Syntax_error (loc, msg) ->
      if opt.interactive then
        Format.fprintf Format.std_formatter "%s%a@\n"
          (if Dolmen.ParseLocation.(loc.start_line = 1) then pre_space else "")
          Dolmen.ParseLocation.fmt_hint loc;
      Format.fprintf Format.std_formatter "%a:@\n%s@." Dolmen.ParseLocation.fmt loc msg;
      if opt.interactive then
        do_commands opt commands
      else
        raise (Exit 1)
  end


(* Main function *)
let () =
  (* Argument parsing *)
  let man = Options.help_secs (Dispatcher.Plugin.ext_doc ()) (Semantics.Addon.ext_doc ()) in
  let info = Cmdliner.Term.(info ~sdocs:Options.copts_sect ~man ~version:"0.1" "archsat") in
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
    Out.set_input_file (input_to_string opt.input_file);
    Out.set_output opt.output_format;

    (* Syntax extensions *)
    Semantics.Addon.set_exts "+base,+arith";
    List.iter Semantics.Addon.set_ext opt.addons;

    (* Extensions options *)
    Dispatcher.Plugin.set_exts "+eq,+uf,+logic,+prop,+skolem,+meta,+inst,+stats,+cstr";
    List.iter Dispatcher.Plugin.set_ext opt.plugins;

    (* Print the current options *)
    start_section 0 "Options";
    Options.log_opts opt;
    Semantics.Addon.log_active 0;
    Dispatcher.Plugin.log_active 0;

    (* Commands execution *)
    begin match opt.input_file with
      | `Stdin ->
        let l, gen = In.parse_input ?language:opt.input_format (`Stdin In.Smtlib) in
        do_commands { opt with input_format = Some l } gen
      | `File f ->
        do_commands opt (Gen.singleton @@ S.include_ f [])
    end;

    (* Output raw profiling data *)
    CCOpt.iter Util.csv_prof_data opt.profile.raw_data;

  with
  | e ->
    delete_alarm ();
    let s = Printexc.get_backtrace () in
    let retcode = match e with
      | Exit ret -> ret
      | Out_of_time ->
        Out.print_timeout Format.std_formatter;
        0
      | Out_of_space ->
        Out.print_spaceout Format.std_formatter;
        0

      (* User interrupt *)
      | Sigint -> 1

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

