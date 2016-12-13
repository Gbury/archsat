
(* ArchSat *)

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
include Ext_constraints

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

  (* Profiling *)
  if opt.profile.enabled then begin
    Util.enable_profiling ();
    Util.Section.set_profile_depth (CCOpt.get 0 opt.profile.max_depth);
    List.iter Util.Section.profile_section opt.profile.sections
  end;
  if opt.profile.print_stats then
    Util.enable_statistics ();

  (* Syntax extensions *)
  Semantics.Addon.set_exts "+base,+arith";
  List.iter Semantics.Addon.set_ext opt.addons;

  (* Extensions options *)
  Dispatcher.Plugin.set_exts "+eq,+uf,+logic,+prop,+skolem,+meta,+inst,+stats,+cstr";
  List.iter Dispatcher.Plugin.set_ext opt.plugins;

  (* Print the current options *)
  Options.log_opts opt;
  Semantics.Addon.log_active 0;
  Dispatcher.Plugin.log_active 0;

  let opt', g = Pipe.parse opt in
  Pipeline.(
    run ~handle_exn:Out.print_exn g opt' (
      expand  Pipe.expand     @@
      op      Pipe.typecheck  @@
      op      Pipe.solve      @@
      iter    Pipe.print_res  @@
      map     fst             @@
      iter    Pipe.print_stats
      @@ pipe_end
    ))

