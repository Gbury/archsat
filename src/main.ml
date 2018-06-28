
(* ArchSat *)

open Options

(* Main function *)
let () =
  (* Register all extensions *)
  Ext.register_all ();
  (* Argument parsing *)
  let man = Options.help_secs (Dispatcher.Plugin.ext_doc ()) (Semantics.Addon.ext_doc ()) in
  let info = Cmdliner.Term.(info ~sdocs:Options.copts_sect ~man ~version:"0.1" "archsat") in
  let opts = Cmdliner.Term.(
      pure (fun () () x -> x)
      $ Semantics.Addon.opts ()
      $ Dispatcher.Plugin.opts ()
      $ (Options.copts_t ())
    ) in
  let opt = match Cmdliner.Term.eval (opts, info) with
    | `Version | `Help -> exit 0
    | `Error `Parse | `Error `Term | `Error `Exn -> exit 1
    | `Ok opt -> opt
  in

  let opt', g =
    try
      (* Set better margins *)
      Format.set_margin 200;
      (* Enable debug mode *)
      if Options.(opt.input.mode = Debug) then
        Util.enable_debug ();

      (* Profiling *)
      if opt.profile.enabled then begin
        at_exit Section.print_profiling_info;
        Section.set_profile_depth
          (CCOpt.get_or ~default:0 opt.profile.max_depth);
        List.iter Section.profile_section opt.profile.sections
      end;

      (* Statistics *)
      if opt.stats.enabled then
        at_exit Stats.print;

      (* Clean state when exiting.
         Called after profiling and statistics to make sure it is called
         before upon exit. *)
      at_exit Util.clean_exit;

      (* Syntax extensions *)
      Semantics.Addon.set_exts "+base,+arith";
      List.iter Semantics.Addon.set_ext opt.addons;

      (* Extensions options *)
      Dispatcher.Plugin.set_exts "+arith,+eq,+inst,+logic,+prop,+skolem,+uf,+stats";
      List.iter Dispatcher.Plugin.set_ext opt.plugins;

      (* Print the current options *)
      Options.log_opts opt;
      Util.log "addons: @[<hov>%a@]"
        CCFormat.(list string) (Semantics.Addon.active ());
      Util.log "plugins: @[<hov>%a@]"
        CCFormat.(list string) (Dispatcher.Plugin.active ());

      (* Initialize proof outputs *)
      Prove.init opt ();

      (* Return the parsor generator *)
      Pipe.parse opt

    with e ->
      if Printexc.backtrace_status () then
        Printexc.print_backtrace stdout;
      Util.error "%a" (Out.print_exn opt) e;
      exit 2
  in
  let opt'' =
    Pipeline.(
      run
        ~finally:(fun opt e ->
            match e with
            | None -> opt
            | Some exn ->
              begin match exn with
                | Options.Sigint
                | Options.Out_of_time
                | Options.Out_of_space ->
                  (** Flushing *and* the break at the start of printing
                      are necessary in case the timeout or other signal interrupted
                      a logger. *)
                  Format.pp_print_flush Format.std_formatter ();
                  Format.printf "@ %a@." (Out.print_exn opt) exn;
                  opt
                | _ ->
                  let () = Util.error "%a" (Out.print_exn opt) exn in
                  Options.error opt
              end)
        g opt' (
        (
          (fix (apply ~name:"expand" Pipe.expand) (
              (apply ~name:"execute" Pipe.execute)
              @>|> (f_map ~name:"typecheck" ~test:Pipe.run_typecheck Pipe.typecheck)
              @>|> (f_map ~name:"solve" Pipe.solve)
              @>|> (iter_ ~name:"print_res" Pipe.print_res)
              @>>> (iter_ ~name:"export" Pipe.export)
              @>>> (iter_ ~name:"print_proof" Pipe.print_proof)
              @>>> (iter_ ~name:"print_model" Pipe.print_model)
              @>>> (apply fst) @>>> _end)
          )
        )
      )
    )
  in
  match opt''.status with
  | Options.Ok -> ()
  | Options.Errored -> exit 1

