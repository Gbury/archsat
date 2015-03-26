
(* TabSat *)

open Options

(* Dummy module renaming for extensions *)
module Eq = Eq
module Tab = Tab
module Prop = Prop
module Functions = Functions
module Skolem = Skolem
module Meta = Meta
module Stats = Stats
module Cnf = Cnf

(* Types and exceptions *)
exception Out_of_time
exception Out_of_space

(* GC alarm for time/space limits *)
let check time_limit size_limit = function () ->
  let t = Sys.time () in
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let s = float heap_size *. float Sys.word_size /. 8. in
  if t > time_limit then
    raise Out_of_time
  else if s > size_limit then
    raise Out_of_space

let al = ref None
let setup_alarm t s = match !al with
  | None -> al := Some (Gc.create_alarm (check t s))
  | Some _ -> assert false

let delete_alarm () = match !al with
  | Some alarm -> Gc.delete_alarm alarm
  | None -> ()

(* Model printing *)
let get_model p_model =
  List.sort (fun (t, _) (t', _) -> Expr.Term.compare t t')
    (match p_model with
     | NoModel -> assert false
     | Simple -> Solver.model ()
     | Full -> Solver.full_model ())

(* Logging *)
let start_section s =
  Util.debug 0 "=== %s %s" s (String.make (64 - String.length s) '=')

let end_section () = ()
(* Util.debug 1 "%s" (String.make 69 '=') *)

let wrap s f x =
  start_section s;
  let res = f x in
  end_section ();
  res

(* Execute given command *)
let do_command opt = function
  | Ast.Sat cnf -> if opt.solve then wrap "assume" Solver.assume cnf
  | Ast.NewType (name, s, n) ->
    wrap ("typing " ^ name) Type.new_type_def (s, n)
  | Ast.TypeDef (name, s, t) ->
    wrap ("typing " ^ name) Type.new_const_def (s, t)
  | Ast.Assert (name, t) ->
    let f = wrap ("typing " ^ name) Type.parse t in
    if opt.solve then wrap "assume" Solver.assume [[f]]
  | Ast.CheckSat ->
    if opt.solve then
      let res = wrap "solve" Solver.solve () in
      begin match res with
        (* Model found *)
        | Solver.Sat ->
          Io.print_res opt.formatter "Sat";
          begin match opt.print_model with
            | NoModel -> ()
            | _ ->
              Io.fprintf opt.formatter "Model :";
              Io.print_model opt.formatter (get_model opt.print_model)
          end
        (* Proof found *)
        | Solver.Unsat ->
          Io.print_res opt.formatter "Unsat";
          if opt.proof then begin
            let proof = Solver.get_proof () in
            begin match opt.print_proof with
            | Some out ->
              Io.print_proof (Format.formatter_of_out_channel out) proof
            | None -> ()
            end
          end
      end
  | c ->
    Io.fprintf opt.formatter "%a : operation not supported yet" Ast.print_command_name c;
    exit 2

(* Main function *)
let main () =
  (* Argument parsing *)
  let man = Options.help_secs (Dispatcher.ext_doc ()) in
  let info = Cmdliner.Term.(info ~sdocs:Options.copts_sect ~man ~version:"0.1" "tabsat") in
  let opt = match Cmdliner.Term.eval (Dispatcher.add_opts (Options.copts_t ()), info) with
    | `Version | `Help | `Error `Parse | `Error `Term | `Error `Exn -> raise Exit
    | `Ok opt -> opt
  in
  (* Gc alarm for limits *)
  setup_alarm opt.time_limit opt.size_limit;
  (* Io options *)
  Io.set_input opt.input_format;
  Io.set_output opt.output_format;
  (* Extensions options *)
  Dispatcher.set_exts "+eq,+uf,+tab,+prop,+skolem,+meta,+inst,+stats";
  List.iter Dispatcher.set_ext opt.extensions;
  (* Input file parsing *)
  let commands = wrap "parse" Io.parse_input opt.input_file in
  (* Commands execution *)
  Queue.iter (do_command opt) commands;
  (* Clean up *)
  Options.clean opt
;;

try
  main ()
with
| Exit -> ()
| Out_of_time ->
  delete_alarm ();
  Io.print_res Format.std_formatter "Timeout"
| Out_of_space ->
  delete_alarm ();
  Io.print_res Format.std_formatter "Out of space"
| Io.Parsing_error (l, msg) ->
  Format.fprintf Format.std_formatter "%a:@\n%s@." ParseLocation.fmt l msg;
  exit 2
| Dispatcher.Extension_not_found s ->
  Format.fprintf Format.std_formatter "Extension '%s' not found. Available extensions are :@\n%a@." s
    (fun fmt -> List.iter (fun s -> Format.fprintf fmt "%s " s)) (Dispatcher.list_extensions ());
  exit 2
| Dispatcher.Bad_assertion s ->
  Format.fprintf Format.std_formatter "%s@." s;
  exit 3
| Expr.Type_error_mismatch (ty1, ty2) ->
  Format.fprintf Format.std_formatter "The following types are NOT compatible :@\n%a ~~ %a@."
    Expr.print_ty ty1 Expr.print_ty ty2;
  exit 4


