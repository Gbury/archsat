
(* Module alias & Helper functions *)
(* ************************************************************************ *)

module S = Dolmen.Statement

(* Logging *)
let start_section ~section (logger: _ Util.logger) s =
  logger ~section "=== %s %s" s (String.make (84 - String.length s) '=')

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
  | `Proof of Solver.proof
  | `Model of Solver.model
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
    if Options.(opt.input.mode = Interactive) then
      Format.printf "%s@?" (Out.prelude opt);
    g ()

let parse opt =
  (** Parse the input *)
  let opt', g =
    match Options.(opt.input.file) with
    | `Stdin ->
      let l, gen = In.parse_input
          ?language:Options.(opt.input.format) (`Stdin In.Smtlib) in
      Options.({ opt with input = { opt.input with format = Some l } }), gen
    | `File f ->
      (** Formats Dimacs and Tptp are descriptive and lack the emission
          of formal solveprove instructions, so we need to add them. *)
      let i = max 0 (CCString.rfind ~sub:"." f) in
      let ext = String.sub f i (String.length f - i) in
      let l, _, _ = In.of_extension ext in
      let s = Dolmen.Statement.include_ f [] in
      let s' =
        match l with
        | In.Dimacs | In.Tptp ->
          Dolmen.Statement.pack [s; Dolmen.Statement.prove ()]
        | _ -> s
      in
      opt, (Gen.singleton s')
  in
  (** Wrap the resulting parser *)
  opt', wrap_parser g

(* Execute statements *)
(* ************************************************************************ *)

let execute (opt, c) =
  match c with
  | { S.descr = S.Exit } -> exit 0
  (** TODO: parse and apply option changes *)
  | _ -> opt, c

(* Expand dolmen statements *)
(* ************************************************************************ *)

let expand (opt, c) =
  match c with
  | { S.descr = S.Pack l } ->
    opt, `Gen (true, Gen.of_list l)
  (* TODO: filter the statements by passing some options *)
  | { S.descr = S.Include f } ->
    let language = Options.(opt.input.format) in
    let dir = Options.(opt.input.dir) in
    begin
      match In.find ?language ~dir f with
      | None -> raise (Options.File_not_found f)
      | Some file ->
        let l, gen = In.parse_input ?language (`File file) in
        let opt' = Options.({
            opt with input = {
            opt.input with format = Some l;
                           file = `File file;
                           mode = Regular }
          } ) in
        opt', `Gen (false, gen)
    end
  | _ -> (opt, `Ok)


(* Typechecking *)
(* ************************************************************************ *)

(* TODO, unwind backtrak stack on exceptions ? *)
let type_wrap ?(goal=false) opt =
  let l = CCOpt.get_exn Options.(opt.input.format) in
  let tys = ref [] in
  let terms = ref [] in
  let status =
    if goal then Expr.Status.goal
    else Expr.Status.hypothesis
  in
  let infer_hook _ = function
    | Type.Ty_fun c -> tys:= c :: !tys
    | Type.Term_fun f -> terms := f :: !terms
  in
  let explain = Options.(opt.typing.explain) in
  let expect =
    match Options.(opt.input.format) with
    | Some In.Tptp -> Type.Typed Expr.Ty.prop
    | _ -> Type.Nothing
  in
  let env = Type.empty_env
      ~status ~explain ~expect
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
    start_section ~section:Type.section Util.info "Definition";
    let env, aux = type_wrap opt in
    let ret = Type.new_def env t id in
    (aux ret :> typechecked stmt)
  | { S.descr = S.Decl (id, t) } ->
    start_section ~section:Type.section Util.info "Declaration typing";
    let env, aux = type_wrap opt in
    let ret = Type.new_decl env t id in
    (aux ret :> typechecked stmt)
  | { S.descr = S.Antecedent t } ->
    start_section ~section:Type.section Util.info "Hypothesis typing";
    let env, aux = type_wrap opt in
    let ret = Type.new_formula env t in
    (aux (`Hyp ret) :> typechecked stmt)
  | { S.descr = S.Consequent t } ->
    start_section ~section:Type.section Util.info "Goal typing";
    let env, aux = type_wrap ~goal:true opt in
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
      start_section ~section:Dispatcher.section Util.info "Assume hyp";
      Solver.assume [[f]]
    end;
    res
  | ({ contents = `Goal f; _ } as res) ->
    if opt.Options.solve then begin
      start_section ~section:Dispatcher.section Util.info "Assume goal";
      Solver.assume [[Expr.Formula.neg f]]
    end;
    res
  | { contents = `Solve; _ } ->
    let ret =
      if opt.Options.solve then begin
        start_section ~section:Dispatcher.section Util.log "Solve";
        begin match Solver.solve () with
          | Solver.Sat m -> `Model m
          | Solver.Unsat p -> `Proof p
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
  | { contents = `Model _; _ } ->
    Util.printf "%a@." Out.print_sat opt
  | { contents = `Proof _; _ } ->
    Util.printf "%a@." Out.print_unsat opt
  | { contents = `Unknown; _ } ->
    Util.printf "%a@." Out.print_unknown opt

(* Printing proofs *)
(* ************************************************************************ *)

let print_proof (opt, (c : solved stmt)) =
  match c with
  | { contents = `Type_def _; _ }
  | { contents = `Term_def _; _ }
  | { contents = `Type_decl _; _ }
  | { contents = `Term_decl _; _ }
  | { contents = `Hyp _; _ }
  | { contents = `Goal _; _ }
  | { contents = `Model _; _ }
  | { contents = `Unknown; _ } ->
    ()
  | { contents = `Proof p; _ } ->
    () (* TODO *)

