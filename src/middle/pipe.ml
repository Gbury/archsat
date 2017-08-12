
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
  | `Type_decl of Expr.ttype Expr.function_descr Expr.id
  | `Term_decl of Expr.ty Expr.function_descr Expr.id
]

type assume = [
  | `Hyp of Expr.formula
  | `Goal of Expr.formula
  | `Clause of Expr.formula list
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
type solved      = [ executed | type_defs | type_decls | assume | result ]

(* Used for represneting typed statements *)
type +'a stmt = {
  id : Dolmen.Id.t;
  contents  : 'a;
  impl_types : Expr.ttype Expr.function_descr Expr.id list;
  impl_terms : Expr.ty Expr.function_descr Expr.id list;
}

let simple id contents = { id; contents; impl_types = []; impl_terms = []; }

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
    if Options.(opt.typing.infer) then
      Type.Typed Expr.Ty.prop
    else match Options.(opt.input.format) with
    | Some In.Tptp -> Type.Typed Expr.Ty.prop
    | Some In.Dimacs -> Type.Typed Expr.Ty.prop
    | _ -> Type.Nothing
  in
  let env = Type.empty_env
      ~status ~explain ~expect
      ~infer_hook (Semantics.type_env l) in
  let aux id res = {
    id;
    impl_types = !tys;
    impl_terms = !terms;
    contents = res;
  } in
  env, aux

let typecheck (opt, c) : typechecked stmt =
  match c with
  (** Declarations and definitions *)
  | { S.descr = S.Def (id, t) } ->
    start_section ~section:Type.section Util.info "Definition";
    let env, aux = type_wrap opt in
    let ret = Type.new_def env t ?attr:c.S.attr id in
    (aux (def_id c) ret :> typechecked stmt)
  | { S.descr = S.Decl (id, t) } ->
    start_section ~section:Type.section Util.info "Declaration typing";
    let env, aux = type_wrap opt in
    let ret = Type.new_decl env t ?attr:c.S.attr id in
    (aux (decl_id c) ret :> typechecked stmt)
  (** Hyps and goal statements *)
  | { S.descr = S.Prove } ->
    simple (prove_id c) `Solve
  | { S.descr = S.Clause l } ->
    start_section ~section:Type.section Util.info "Clause typing";
    let env, aux = type_wrap opt in
    let res = List.map (Type.new_formula env) l in
    (aux (hyp_id c) (`Clause res) :> typechecked stmt)
  | { S.descr = S.Antecedent t } ->
    start_section ~section:Type.section Util.info "Hypothesis typing";
    let env, aux = type_wrap opt in
    let ret = Type.new_formula env t in
    (aux (hyp_id c) (`Hyp ret) :> typechecked stmt)
  | { S.descr = S.Consequent t } ->
    start_section ~section:Type.section Util.info "Goal typing";
    let env, aux = type_wrap ~goal:true opt in
    let ret = Type.new_formula env t in
    (aux (goal_id c) (`Goal ret) :> typechecked stmt)
  (** We can safely ignore set-logic "dimacs", as it only gives the number of atoms
      and clauses of the dimacs problem, which is of no interest. *)
  | { S.descr = S.Set_logic "dimacs" } ->
    simple none `Executed

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
    if opt.Options.solve then begin
      start_section ~section:Dispatcher.section Util.info "Assume clause";
      Solver.assume c.id l
    end;
    res
  | ({ contents = `Hyp f; _ } as res) ->
    if opt.Options.solve then begin
      start_section ~section:Dispatcher.section Util.info "Assume hyp";
      Solver.assume c.id [f]
    end;
    res
  | ({ contents = `Goal f; _ } as res) ->
    if opt.Options.solve then begin
      start_section ~section:Dispatcher.section Util.info "Assume goal";
      Solver.assume c.id [Expr.Formula.neg f]
    end;
    res
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
  | { contents = `Hyp _; _ }
  | { contents = `Goal _; _ }
  | { contents = `Clause _; _ } ->
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
  | { contents = `Hyp _; _ }
  | { contents = `Goal _; _ }
  | { contents = `Clause _; _ }
  | { contents = `Unknown; _ } ->
    ()
  | { contents = `Model _; _ }
  | { contents = `Proof _; _ } ->
    pp_opt Solver.export_dimacs Options.(opt.output.dimacs) ()

(* Printing proofs *)
(* ************************************************************************ *)

let declare_implicits opt c =
  if c.impl_types <> [] && c.impl_terms <> [] &&
     not Options.(opt.proof.context) then
    Util.warn "The following symbols are implictly typed: @[<hov>%a%a%a@]"
      CCFormat.(list ~sep:(return ",@ ") Expr.Print.const_ttype) c.impl_types
      CCFormat.(return (if c.impl_types <> [] && c.impl_terms <> [] then ",@ " else "")) ()
      CCFormat.(list ~sep:(return ",@ ") Expr.Print.const_ty) c.impl_terms
  else begin
    List.iter (fun v ->
        pp_opt Coq.declare_ty Options.(opt.proof.coq) v) c.impl_types;
    List.iter (fun v ->
        pp_opt Coq.declare_term Options.(opt.proof.coq) v) c.impl_terms;
    ()
  end

let print_proof (opt, (c : solved stmt)) =
  let () = declare_implicits opt c in
  match c with
  (* Not much to do with these... *)
  | { contents = `Executed; _ }
  | { contents = `Type_def _; _ }
  | { contents = `Term_def _; _ }
  | { contents = `Model _; _ }
  | { contents = `Unknown; _ } -> ()

  (* Interesting parts *)
  | { contents = `Type_decl f; _ } ->
    if Options.(opt.proof.context) then
      pp_opt Coq.declare_ty Options.(opt.proof.coq) f;
    ()
  | { contents = `Term_decl f; _ } ->
    if Options.(opt.proof.context) then
      pp_opt Coq.declare_term Options.(opt.proof.coq) f;
    ()
  | { contents = `Clause l ; id; _ } ->
    let h = Expr.Formula.f_or l in
    if Options.(opt.proof.context) then
      pp_opt Coq.add_hyp Options.(opt.proof.coq) (id, h);
    ()
  | { contents = `Hyp h; id; _ } ->
    if Options.(opt.proof.context) then
      pp_opt Coq.add_hyp Options.(opt.proof.coq) (id, h);
    ()
  | { contents = `Goal g; id; _ } ->
    if Options.(opt.proof.context) then
      pp_opt Coq.add_goal Options.(opt.proof.coq) (id, g);
    ()
  | { contents = `Proof p; _ } ->
    let () = pp_opt Unsat_core.print Options.(opt.proof.unsat_core) p in
    let () = pp_opt Dot.print Options.(opt.proof.dot) p in
    let () = pp_opt Coq.print_proof Options.(opt.proof.coq) p in
    ()

