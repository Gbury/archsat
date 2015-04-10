
let id = Dispatcher.new_id ()
let log_section = Util.Section.make "cnf"
let log i fmt = Util.debug ~section:log_section i fmt

(* Local environments *)
(* ************************************************************************ *)

type env = {
  num : int;
  truth : bool;
  type_vars : Expr.ty_subst;
  term_vars : Expr.term_subst;
}

let empty_env = {
  num = 0;
  truth = true;
  type_vars = Expr.Subst.empty;
  term_vars = Expr.Subst.empty;
}

let split env = env, { env with num = env.num + 1 }
let negate env = { env with truth = not env.truth }
let apply env t = Expr.term_subst env.type_vars env.term_vars t

let name env s =
  assert (env.num > 0);
  let suffix = String.make env.num '\'' in
  s ^ suffix

let add_ty_var env v =
  let ty =
    if env.num <= 0 then Expr.type_var v
    else Expr.(type_var (ttype_var (name env v.var_name)))
  in
  log 10 "%a -> %a" Expr.debug_var_ttype v Expr.debug_ty ty;
  { env with type_vars = Expr.Subst.Var.bind v ty env.type_vars }

let add_term_var env v =
  let t =
    if env.num <= 0 then Expr.term_var v
    else Expr.(term_var (ty_var (name env v.var_name) v.var_type))
  in
  log 10 "%a -> %a" Expr.debug_var_ty v Expr.debug_term t;
  { env with term_vars = Expr.Subst.Var.bind v t env.term_vars }

let add_ty_vars = List.fold_left add_ty_var
let add_term_vars = List.fold_left add_term_var

let add_ty_sk env vars (ty_args, t_args) =
  assert (t_args = []);
  let ty_args = List.map (Expr.type_subst env.type_vars) ty_args in
  { env with type_vars = List.fold_left (fun s v ->
        Expr.Subst.Var.bind v (Expr.type_app (Expr.get_ty_skolem v) ty_args) s) env.type_vars vars }

let add_term_sk env vars (ty_args, t_args) =
  let ty_args = List.map (Expr.type_subst env.type_vars) ty_args in
  let t_args = List.map (apply env) t_args in
  { env with term_vars = List.fold_left (fun s v ->
        Expr.Subst.Var.bind v (Expr.term_app (Expr.get_term_skolem v) ty_args t_args) s) env.term_vars vars }

(* Free variables disjonction *)
(* ************************************************************************ *)

let disjoint l l' =
  not (List.exists (fun v -> List.exists (Expr.Var.equal v) l') l)

let fv_disjoint ((tys, ts), (tys', ts')) = disjoint tys tys' && disjoint ts ts'

let fv_disjoint_list l = List.for_all fv_disjoint (Util.list_diagonal l)

(* Prenex form *)
(* ************************************************************************ *)

let apply_truth truth f = if truth then f else Expr.f_not f

let pred env p = apply_truth env.truth (Expr.f_pred (apply env p))
let equal env a b = apply_truth env.truth (Expr.f_equal (apply env a) (apply env b))

let mk_or env = if env.truth then Expr.f_or else Expr.f_and
let mk_and env = if env.truth then Expr.f_and else Expr.f_or

let rec specialize env = function
  (* Base formulas *)
  | { Expr.formula = Expr.Pred p } -> pred env p
  | { Expr.formula = Expr.Equal (a, b) } -> equal env a b
  | { Expr.formula = Expr.True } -> apply_truth env.truth Expr.f_true
  | { Expr.formula = Expr.False } -> apply_truth env.truth Expr.f_false

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
    mk_and env [specialize env' (Expr.f_imply p q);
                specialize env'' (Expr.f_imply q p)]
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
    when fv_disjoint_list (List.map Expr.formula_fv l) ->
    Expr.f_and (List.map generalize l)
  | { Expr.formula = Expr.Or l }
    when fv_disjoint_list (List.map Expr.formula_fv l) ->
    Expr.f_or (List.map generalize l)
  | f ->
    let ty_vars, t_vars = Expr.formula_fv f in
    log 15 "generalizing : %a" Expr.debug_formula f;
    log 15 "Free_vars :";
    List.iter (fun v -> log 15 " |- %a" Expr.debug_var_ttype v) ty_vars;
    List.iter (fun v -> log 15 " |- %a" Expr.debug_var_ty v) t_vars;
    Expr.f_allty ty_vars (Expr.f_all t_vars f)

let prenex = function
  (*
  | ({ Expr.formula = Expr.Not { Expr.formula = Expr.Equiv _ } } as f)
  | ({ Expr.formula = Expr.Equiv _ } as f) -> f
     *)
  | f -> generalize (specialize empty_env f)

let do_formula f =
  let f' = prenex f in
  log 5 "from : %a" Expr.debug_formula f;
  if Expr.Formula.equal f f' then begin
    log 5 "not changed.";
    None
  end else begin
    log 5 "to   : %a" Expr.debug_formula f';
    Some (f', Dispatcher.mk_proof id "todo")
  end

;;
Dispatcher.(register (
    mk_ext
      ~descr:"Pre-process formulas to put them in cnf and/or prenex normal form"
      ~preprocess:do_formula
      id "cnf"
  ))
