
(* Module alias & Helper functions *)
(* ************************************************************************ *)

module S = Dolmen.Statement

(* Logging *)
let start_section ~section (logger: _ Util.logger) s =
  logger ~section "=== %s %s" s (String.make (84 - String.length s) '=')

(* Printing on optional formatters *)
let pp_opt pp o x =
  match o with
  | None -> ()
  | Some fmt -> pp fmt x

(* Types used in Pipes *)
(* ************************************************************************ *)

(* Typechecked statements *)
type executed = [ `Executed ]

type type_defs = [
  | `Type_def of Dolmen.Id.t * Expr.ttype Expr.id list * Expr.ty
  | `Term_def of Dolmen.Id.t * Expr.ttype Expr.id list * Expr.ty Expr.id list * Expr.term
]

type type_decls = [
  | `Type_decl of Expr.Id.TyCstr.t
  | `Term_decl of Expr.Id.Const.t
]

type assume = [
  | `Hyp of Expr.formula
  | `Goal of Expr.formula
  | `Clause of Expr.formula list
]

type sequent = [
  | `Left of Solver.id * Expr.formula
  | `Right of Solver.id * Expr.formula
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
type typechecked = [ executed | type_defs | type_decls | assume | solve ]
type solved      = [ executed | type_defs | type_decls | sequent | result ]

(* Used for represneting typed statements *)
type +'a stmt = {
  id : Dolmen.Id.t;
  contents  : 'a;
  loc : Dolmen.ParseLocation.t option;
}

let simple id loc contents = { id; loc; contents; }

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
      let l, gen, _ = In.parse_input
          ?language:Options.(opt.input.format) (`Stdin In.Smtlib) in
      Options.({ opt with input = { opt.input with format = Some l } }), gen
    | `File f ->
      (** Formats Dimacs and Tptp are descriptive and lack the emission
          of formal solve/prove instructions, so we need to add them. *)
      let s = Dolmen.Statement.include_ f [] in
      (* Auto-detect input format *)
      let l =
        match Options.(opt.input.format) with
        | Some l -> l
        | None ->
          let res, _, _ = In.of_filename f in
          res
      in
      let s' =
        match l with
        | In.Zf
        | In.ICNF
        | In.Smtlib -> s
        | In.Dimacs
        | In.Tptp ->
          Dolmen.Statement.pack [s; Dolmen.Statement.prove ()]
      in
      Options.({ opt with input = { opt.input with format = Some l } }),
      (Gen.singleton s')
  in
  (** Wrap the resulting parser *)
  opt', wrap_parser g

(* Execute statements *)
(* ************************************************************************ *)

let none = Dolmen.Id.mk Dolmen.Id.decl "<>"

let execute (opt, c) =
  match c with
  (** Exit the prover, no need to return a statement. *)
  | { S.descr = S.Exit } -> exit 0
  (** TODO: parse and apply option changes *)
  | _ -> `Continue (opt, c)

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
        (* TODO: cleanup files after having read them ?
           only useful if there happens to be a very long long
           (i.e. at least a few thousands) chain of nested includes) *)
        let l, gen, _ = In.parse_input ?language (`File file) in
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

let stmt_id ref_name =
  let counter = ref 0 in
  (fun c ->
     match c.Dolmen.Statement.id with
     | { Dolmen.Id.ns = Dolmen.Id.Decl; name = "" } ->
       let () = incr counter in
       let name = Format.sprintf "%s_%d" ref_name !counter in
       Dolmen.Id.mk Dolmen.Id.decl name
     | id -> id)

let def_id   = stmt_id "def"
let decl_id  = stmt_id "decl"
let hyp_id   = stmt_id "hyp"
let goal_id  = stmt_id "goal"
let prove_id = stmt_id "prove"

(* TODO, unwind backtrak stack on exceptions ? *)
let type_wrap ?(goal=false) opt =
  let l = CCOpt.get_exn Options.(opt.input.format) in
  let status =
    if goal then Expr.Status.goal
    else Expr.Status.hypothesis
  in
  let explain = Options.(opt.typing.explain) in
  let expect =
    if Options.(opt.typing.infer) then
      Type.Typed Expr.Ty.prop
    else match Options.(opt.input.format) with
    | Some In.Tptp -> Type.Typed Expr.Ty.prop
    | Some In.Dimacs -> Type.Typed Expr.Ty.prop
    | _ -> Type.Nothing
  in
  let env = Type.empty_env
      ~status ~explain ~expect
      (Semantics.type_env l)
  in
  env

let run_typecheck opt = Options.(opt.typing.typing)

let typecheck (opt, c) : typechecked stmt =
  match c with
  (** Declarations and definitions *)
  | { S.descr = S.Def (id, t) } ->
    start_section ~section:Type.section Util.debug "Definition";
    let env = type_wrap opt in
    let ret = Type.new_def env t ?attr:c.S.attr id in
    (simple (def_id c) c.S.loc ret :> typechecked stmt)
  | { S.descr = S.Decl (id, t) } ->
    start_section ~section:Type.section Util.debug "Declaration typing";
    let env = type_wrap opt in
    let ret = Type.new_decl env t ?attr:c.S.attr id in
    (simple (decl_id c) c.S.loc ret :> typechecked stmt)
  (** Hyps and goal statements *)
  | { S.descr = S.Prove } ->
    simple (prove_id c) c.S.loc `Solve
  | { S.descr = S.Clause l } ->
    start_section ~section:Type.section Util.debug "Clause typing";
    let env = type_wrap opt in
    let res = List.map (Type.new_formula env) l in
    (simple (hyp_id c) c.S.loc (`Clause res) :> typechecked stmt)
  | { S.descr = S.Antecedent t } ->
    start_section ~section:Type.section Util.debug "Hypothesis typing";
    let env = type_wrap opt in
    let ret = Type.new_formula env t in
    (simple (hyp_id c) c.S.loc (`Hyp ret) :> typechecked stmt)
  | { S.descr = S.Consequent t } ->
    start_section ~section:Type.section Util.debug "Goal typing";
    let env = type_wrap ~goal:true opt in
    let ret = Type.new_formula env t in
    (simple (goal_id c) c.S.loc (`Goal ret) :> typechecked stmt)
  (** We can safely ignore set-logic "dimacs", as it only gives the number of atoms
      and clauses of the dimacs problem, which is of no interest. *)
  | { S.descr = S.Set_logic "dimacs" } ->
    simple none c.S.loc `Executed
  (** Other set_logics should check whether corresponding plugins are activated ? *)
  | { S.descr = S.Set_logic _ } -> simple none c.S.loc `Executed
  (** Set info can always be ignored. *)
  | { S.descr = S.Set_info _ } -> simple none c.S.loc `Executed

  (** Other untreated statements *)
  | _ -> raise (Options.Stmt_not_implemented c)

(* Solving *)
(* ************************************************************************ *)

let solve (opt, (c : typechecked stmt)) : solved stmt =
  match c with
  | ({contents = `Executed; _ } as res)
  | ({ contents = `Type_def _; _ } as res)
  | ({ contents = `Term_def _; _ } as res)
  | ({ contents = `Type_decl _; _ } as res)
  | ({ contents = `Term_decl _; _ } as res) ->
    res
  | ({ contents = `Clause l; _ } as res) ->
    start_section ~section:Dispatcher.section Util.debug "Assume clause";
    let id = Solver.assume ~solve:Options.(opt.solve) l in
    let f = Expr.Formula.f_or l in
    (simple res.id res.loc (`Left (id, f)) :> solved stmt)
  | ({ contents = `Hyp f; _ } as res) ->
    start_section ~section:Dispatcher.section Util.debug "Assume hyp";
    let id = Solver.assume ~solve:Options.(opt.solve) [f] in
    (simple res.id res.loc (`Left (id, f)) :> solved stmt)
  | ({ contents = `Goal f; _ } as res) ->
    start_section ~section:Dispatcher.section Util.info "Assume goal";
    let id = Solver.assume ~solve:Options.(opt.solve)
        [Expr.Formula.neg ~status:Expr.Status.goal f] in
    (simple res.id res.loc (`Right (id, f)) :> solved stmt)
  | { contents = `Solve; _ } ->
    let ret =
      if opt.Options.solve then begin
        start_section ~section:Dispatcher.section Util.log "Solve";
        let check_model = Options.(opt.model.active) in
        let check_proof = Options.(opt.proof.active) in
        let export = Options.(opt.output.icnf) in
        begin match Solver.solve ~check_model ~check_proof ?export () with
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
  | { contents = `Executed; _ }
  | { contents = `Type_def _; _ }
  | { contents = `Term_def _; _ }
  | { contents = `Type_decl _; _ }
  | { contents = `Term_decl _; _ }
  | { contents = `Left _; _ }
  | { contents = `Right _; _ } ->
    ()
  | { contents = `Model _; _ } ->
    Util.printf "%a@." Out.print_sat opt
  | { contents = `Proof _; _ } ->
    Util.printf "%a@." Out.print_unsat opt
  | { contents = `Unknown; _ } ->
    Util.printf "%a@." Out.print_unknown opt

(* Export information *)
(* ************************************************************************ *)

let export (opt, (c : solved stmt)) =
  match c with
  | { contents = `Executed; _ }
  | { contents = `Type_def _; _ }
  | { contents = `Term_def _; _ }
  | { contents = `Type_decl _; _ }
  | { contents = `Term_decl _; _ }
  | { contents = `Left _; _ }
  | { contents = `Right _; _ }
  | { contents = `Unknown; _ } ->
    ()
  | { contents = `Model _; _ }
  | { contents = `Proof _; _ } ->
    pp_opt Solver.export_dimacs Options.(opt.output.dimacs) ()

(* Printing proofs *)
(* ************************************************************************ *)

let print_proof (opt, (c : solved stmt)) =
  match c with
  (* Not much to do with these... *)
  | { contents = `Executed; _ }
  | { contents = `Type_def _; _ }
  | { contents = `Term_def _; _ } -> ()
  | { contents = `Model _; _ } ->
    if Options.(opt.proof.active) then
      Util.warn "Proof check/output activated, but a model was found"
  | { contents = `Unknown; _ } ->
    if Options.(opt.proof.active) then
      Util.warn "Proof check/output activated, but no proof was found"

  (* Interesting parts *)
  | { contents = `Type_decl f; _ } ->
    Prove.declare_ty ?loc:c.loc Options.(opt.proof) f
  | { contents = `Term_decl f; _ } ->
    Prove.declare_term ?loc:c.loc Options.(opt.proof) f
  | { contents = `Left (hyp_id, f) ; id; _ } ->
    let t = Prove.declare_hyp ?loc:c.loc Options.(opt.proof) id f in
    Solver.register_hyp hyp_id t
  | { contents = `Right (hyp_id, f); id; _ } ->
    let _ = Prove.declare_goal ?loc:c.loc Options.(opt.proof) id f in
    ()
  | { contents = `Proof p; _ } ->
    Util.info "Proof size: %a" Util.print_size (Util.size p);
    Prove.output_proof Options.(opt.proof) p

(* Printing models *)
(* ************************************************************************ *)

let print_model (opt, (c : solved stmt)) =
  match c with
  | { contents = `Executed; _ }
  | { contents = `Type_def _; _ }
  | { contents = `Term_def _; _ }
  | { contents = `Type_decl _; _ }
  | { contents = `Term_decl _; _ }
  | { contents = `Left _; _ }
  | { contents = `Right _ } -> ()
  | { contents = `Proof _; _ } ->
    if Options.(opt.model.active) then
      Util.warn "Model check/output activated, but a proof was found"
  | { contents = `Unknown; _ } ->
    if Options.(opt.model.active) then
      Util.warn "Model check/output activated, but no model was found"

  (* Interesting parts *)
  | { contents = `Model m; _ } ->
    Util.info "Model size: %a" Util.print_size (Util.size m);
    pp_opt Solver.Model.print Options.(opt.model.assign) m

