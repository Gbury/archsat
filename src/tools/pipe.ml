
(* Module alias & Helper functions *)
(* ************************************************************************ *)

module S = Dolmen.Statement

(* Logging *)
let start_section l s =
  Util.debug l "=== %s %s" s (String.make (64 - String.length s) '=')

(* Types used in Pipes *)
(* ************************************************************************ *)

(* Typechecked statements *)
type type_defs = [
  | `Type_def of Dolmen.Id.t * Expr.ttype Expr.id list * Expr.ty
  | `Term_def of Dolmen.Id.t * Expr.ttype Expr.id list * Expr.ty Expr.id list * Expr.term
]

type type_decls = [
  | `Type_decl of Expr.ttype Expr.function_descr Expr.id
  | `Term_decl of Expr.ty Expr.function_descr Expr.id
]

type assume = [
  | `Hyp of Expr.formula
  | `Goal of Expr.formula
]

type solve = [
  | `Solve
]

type result = [
  | `Unknown
  | `Proof (* TODO: add proof payload *)
  | `Model (* TODO: add model payload *)
]

(* Agregate types *)
type typechecked = [ type_defs | type_decls | assume | solve ]
type solved      = [ type_defs | type_decls | assume | result ]

(* Used for represneting typed statements *)
type +'a stmt = {
  impl_types : Expr.ttype Expr.function_descr Expr.id list;
  impl_terms : Expr.ty Expr.function_descr Expr.id list;
  contents  : 'a;
}

let simple contents = { contents; impl_types = []; impl_terms = []; }

(* Parsing *)
(* ************************************************************************ *)

let wrap_parser g =
  fun opt ->
    if opt.Options.interactive then
      Format.printf "%s@?" (Out.prelude opt);
    g ()

let parse opt =
  (** Parse the input *)
  let opt', g =
    match opt.Options.input_file with
    | `Stdin ->
      let l, gen = In.parse_input
          ?language:opt.Options.input_format (`Stdin In.Smtlib) in
      { opt with Options.input_format = Some l }, gen
    | `File f ->
      opt, (Gen.singleton @@ Dolmen.Statement.include_ f [])
  in
  (** Formats Dimacs and Tptp are descriptive and lack the emission
      of formal solveprove instructions, so we need to add them. *)
  let g' =
    match opt'.Options.input_format with
    | Some In.Dimacs | Some In.Tptp ->
      Gen.append g (Gen.singleton @@ S.prove ())
    | _ -> g
  in
  (** Wrap the resulting parser *)
  opt', wrap_parser g'

(* Execute statements *)
(* ************************************************************************ *)

let execute (opt, c) =
  match c with
  | { S.descr = S.Exit } -> exit 0
  (** TODO: parse and apply option changes *)
  | _ -> opt, c

(* Expand dolmen statements *)
(* ************************************************************************ *)

let expand_pack (opt, c) =
  match c with
  | { S.descr = S.Pack l } ->
    opt, Gen.of_list l
  | _ -> opt, Gen.singleton c

let expand_include (opt, c) =
  match c with
  (* TODO: filter the statements by passing some options *)
  | { S.descr = S.Include f } ->
    let language = opt.Options.input_format in
    let dir = opt.Options.input_dir in
    begin
      match In.find ?language ~dir f with
      | None -> raise (Options.File_not_found f)
      | Some file ->
        let l, gen = In.parse_input ?language (`File file) in
        let opt' = Options.{ opt with
                             input_format = Some l;
                             input_file = `File file;
                             interactive = false } in
        opt', `Gen gen
    end
  | _ -> (opt, `Ok)


(* Typechecking *)
(* ************************************************************************ *)

(* TODO, unwind backtrak stack on exceptions *)
let type_wrap opt =
  let l = CCOpt.get_exn opt.Options.input_format in
  let tys = ref [] in
  let terms = ref [] in
  let infer_hook = function
    | `Ty c -> tys:= c :: !tys
    | `Term f -> terms := f :: !terms
  in
  let env = Type.empty_env
      ~status:Expr.Status.hypothesis
      ~infer_hook (Semantics.type_env l) in
  let aux res = {
    impl_types = !tys;
    impl_terms = !terms;
    contents = res;
  } in
  env, aux

let typecheck (opt, c) : typechecked stmt =
  match c with
  | { S.descr = S.Def (id, t) } ->
    start_section 0 "Definition";
    let env, aux = type_wrap opt in
    let ret = Type.new_def env t id in
    (aux ret :> typechecked stmt)
  | { S.descr = S.Decl (id, t) } ->
    start_section 0 "Declaration";
    let env, aux = type_wrap opt in
    let ret = Type.new_decl env t id in
    (aux ret :> typechecked stmt)
  | { S.descr = S.Antecedent t } ->
    start_section 0 "Hypothesis typing";
    let env, aux = type_wrap opt in
    let ret = Type.new_formula env t in
    (aux (`Hyp ret) :> typechecked stmt)
  | { S.descr = S.Consequent t } ->
    start_section 0 "Hypothesis typing";
    let env, aux = type_wrap opt in
    let ret = Type.new_formula env t in
    (aux (`Goal ret) :> typechecked stmt)
  | { S.descr = S.Prove } ->
    simple `Solve
  | _ ->
    raise (Options.Stmt_not_implemented c)

(* Solving *)
(* ************************************************************************ *)

let solve (opt, (c : typechecked stmt)) : solved stmt =
  match c with
  | ({ contents = `Type_def _; _ } as res)
  | ({ contents = `Term_def _; _ } as res)
  | ({ contents = `Type_decl _; _ } as res)
  | ({ contents = `Term_decl _; _ } as res) ->
    res
  | ({ contents = `Hyp f; _ } as res) ->
    if opt.Options.solve then begin
      start_section 0 "Assume hyp";
      Solver.assume [[f]]
    end;
    res
  | ({ contents = `Goal f; _ } as res) ->
    if opt.Options.solve then begin
      start_section 0 "Assume goal";
      Solver.assume [[Expr.Formula.neg f]]
    end;
    res
  | { contents = `Solve; _ } ->
    let ret =
      if opt.Options.solve then begin
        start_section 0 "Solve";
        begin match Solver.solve () with
          | Solver.Sat _ -> `Model
          | Solver.Unsat _ -> `Proof
          | Solver.Unknown -> `Unknown
        end
      end else
        `Unknown
    in
    { c with contents = ret }

(* Printing results *)
(* ************************************************************************ *)

let print_res (opt, (c : solved stmt)) =
  match c with
  | { contents = `Type_def _; _ }
  | { contents = `Term_def _; _ }
  | { contents = `Type_decl _; _ }
  | { contents = `Term_decl _; _ }
  | { contents = `Hyp _; _ }
  | { contents = `Goal _; _ } ->
    ()
  | { contents = `Model; _ }->
    Out.print_sat opt
  | { contents = `Proof; _ }->
    Out.print_unsat opt
  | { contents = `Unknown; _ }->
    Out.print_unknown opt

(* Printing stats *)
(* ************************************************************************ *)

let print_stats opt =
  CCOpt.iter Util.csv_prof_data Options.(opt.profile.raw_data)

