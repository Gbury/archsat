
let id = Dispatcher.new_id ()
let log_section = Util.Section.make "cnf"
let log i fmt = Util.debug ~section:log_section i fmt

(* Local environments *)
(* ************************************************************************ *)

type env = {
  num : int;
  truth : bool;
  type_vars : Expr.Ty.subst;
  term_vars : Expr.Term.subst;
}

let empty_env = {
  num = 0;
  truth = true;
  type_vars = Expr.Subst.empty;
  term_vars = Expr.Subst.empty;
}

let split env = env, { env with num = env.num + 1 }
let negate env = { env with truth = not env.truth }
let apply env t = Expr.Term.subst env.type_vars env.term_vars t

let name env s =
  assert (env.num > 0);
  let suffix = String.make env.num '\'' in
  s ^ suffix

let add_ty_var env v =
  let ty =
    if env.num <= 0 then Expr.Ty.of_var v
    else Expr.(Ty.of_var (Id.ttype (name env v.id_name)))
  in
  log 10 "%a -> %a" Expr.Debug.id_ttype v Expr.Debug.ty ty;
  { env with type_vars = Expr.Subst.Id.bind v ty env.type_vars }

let add_term_var env v =
  let t =
    if env.num <= 0 then Expr.Term.of_var v
    else Expr.(Term.of_var (Id.ty (name env v.id_name) v.id_type))
  in
  log 10 "%a -> %a" Expr.Debug.id_ty v Expr.Debug.term t;
  { env with term_vars = Expr.Subst.Id.bind v t env.term_vars }

let add_ty_vars = List.fold_left add_ty_var
let add_term_vars = List.fold_left add_term_var

let add_ty_sk env vars (ty_args, t_args) =
  assert (t_args = []);
  let ty_args = List.map (Expr.Ty.subst env.type_vars) ty_args in
  { env with type_vars = List.fold_left (fun s v ->
        Expr.Subst.Id.bind v (Expr.Ty.apply (Expr.Id.ty_skolem v) ty_args) s) env.type_vars vars }

let add_term_sk env vars (ty_args, t_args) =
  let ty_args = List.map (Expr.Ty.subst env.type_vars) ty_args in
  let t_args = List.map (apply env) t_args in
  { env with term_vars = List.fold_left (fun s v ->
        Expr.Subst.Id.bind v (Expr.Term.apply (Expr.Id.term_skolem v) ty_args t_args) s) env.term_vars vars }

(* Free variables disjonction *)
(* ************************************************************************ *)

let disjoint l l' =
  not (List.exists (fun v -> List.exists (Expr.Id.equal v) l') l)

let fv_disjoint ((tys, ts), (tys', ts')) = disjoint tys tys' && disjoint ts ts'

let fv_disjoint_list l = List.for_all fv_disjoint (CCList.diagonal l)

(* Prenex form *)
(* ************************************************************************ *)

let apply_truth truth f = if truth then f else Expr.Formula.neg f

let pred env p = apply_truth env.truth (Expr.Formula.pred (apply env p))
let equal env a b = apply_truth env.truth (Expr.Formula.eq (apply env a) (apply env b))

let mk_or env = if env.truth then Expr.Formula.f_or else Expr.Formula.f_and
let mk_and env = if env.truth then Expr.Formula.f_and else Expr.Formula.f_or

let rec specialize env = function
  (* Base formulas *)
  | { Expr.formula = Expr.Pred p } -> pred env p
  | { Expr.formula = Expr.Equal (a, b) } -> equal env a b
  | { Expr.formula = Expr.True } -> apply_truth env.truth Expr.Formula.f_true
  | { Expr.formula = Expr.False } -> apply_truth env.truth Expr.Formula.f_false

  (* Logical connectives *)
  | { Expr.formula = Expr.Not p } -> specialize (negate env) p
  | { Expr.formula = Expr.And l } -> mk_and env (List.map (specialize env) l)
  | { Expr.formula = Expr.Or l } -> mk_or env (List.map (specialize env) l)
  | { Expr.formula = Expr.Imply (p, q) } ->
    let p' = specialize (negate env) p in
    let q' = specialize env q in
    mk_or env [p'; q']
  | { Expr.formula = Expr.Equiv (p, q) } ->
    let env', env'' = split env in
    mk_and env [specialize env' (Expr.Formula.imply p q);
                specialize env'' (Expr.Formula.imply q p)]
  (* Quantifications *)
  | { Expr.formula = Expr.All (l, args, p) } ->
    let env' =
      if env.truth then
        add_term_vars env l
      else
        add_term_sk env l args
    in
    specialize env' p
  | { Expr.formula = Expr.AllTy (l, args, p) } ->
    let env' =
      if env.truth then
        add_ty_vars env l
      else
        add_ty_sk env l args
    in
    specialize env' p
  | { Expr.formula = Expr.Ex (l, args, p) } ->
    let env' =
      if env.truth then
        add_term_sk env l args
      else
        add_term_vars env l
    in
    specialize env' p
  | { Expr.formula = Expr.ExTy (l, args, p) } ->
    let env' =
      if env.truth then
        add_ty_sk env l args
      else
        add_ty_vars env l
    in
    specialize env' p

let rec generalize = function
  | { Expr.formula = Expr.And l }
    when fv_disjoint_list (List.map Expr.Formula.fv l) ->
    Expr.Formula.f_and (List.map generalize l)
  | { Expr.formula = Expr.Or l }
    when fv_disjoint_list (List.map Expr.Formula.fv l) ->
    Expr.Formula.f_or (List.map generalize l)
  | f ->
    let ty_vars, t_vars = Expr.Formula.fv f in
    log 15 "generalizing : %a" Expr.Debug.formula f;
    log 15 "Free_vars :";
    List.iter (fun v -> log 15 " |- %a" Expr.Debug.id_ttype v) ty_vars;
    List.iter (fun v -> log 15 " |- %a" Expr.Debug.id_ty v) t_vars;
    Expr.Formula.allty ty_vars (Expr.Formula.all t_vars f)

let prenex = function
  (*
  | ({ Expr.formula = Expr.Not { Expr.formula = Expr.Equiv _ } } as f)
  | ({ Expr.formula = Expr.Equiv _ } as f) -> f
     *)
  | f -> generalize (specialize empty_env f)

let do_formula f =
  let f' = prenex f in
  log 5 "from : %a" Expr.Debug.formula f;
  if Expr.Formula.equal f f' then begin
    log 5 "not changed.";
    None
  end else begin
    log 5 "to   : %a" Expr.Debug.formula f';
    Some (f', Dispatcher.mk_proof id "todo")
  end

;;
Dispatcher.(register (
    mk_ext
      ~descr:"Pre-process formulas to put them in cnf and/or prenex normal form"
      ~preprocess:do_formula
      id "cnf"
  ))
