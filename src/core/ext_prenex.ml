(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

let section = Section.make ~parent:Dispatcher.section "prenex"

type lemma_info = TODO

type Dispatcher.lemma_info += Prenex of lemma_info

(* Local environments *)
(* ************************************************************************ *)

type env = {
  num : int;
  truth : bool;
  type_vars : Expr.Ty.var_subst;
  term_vars : Expr.Term.var_subst;
}

let empty_env = {
  num = 0;
  truth = true;
  type_vars = Expr.Subst.empty;
  term_vars = Expr.Subst.empty;
}

let split env = env, { env with num = env.num + 1 }

let negate env = { env with truth = not env.truth }

let apply env t =
  Expr.Term.subst env.type_vars Expr.Subst.empty env.term_vars Expr.Subst.empty t

let name env s =
  assert (env.num > 0);
  let suffix = String.make env.num '\'' in
  s ^ suffix

let add_ty_var env v =
  let ty =
    if env.num <= 0 then Expr.Ty.of_id v
    else Expr.(Ty.of_id (Id.ttype (name env v.id_name)))
  in
  Util.debug ~section "%a -> %a" Expr.Print.id_ttype v Expr.Print.ty ty;
  { env with type_vars = Expr.Subst.Id.bind env.type_vars v ty }

let add_term_var env v =
  let t =
    if env.num <= 0 then Expr.Term.of_id v
    else Expr.(Term.of_id (Id.ty (name env v.id_name) v.id_type))
  in
  Util.debug ~section "%a -> %a" Expr.Print.id_ty v Expr.Print.term t;
  { env with term_vars = Expr.Subst.Id.bind env.term_vars v t }

let add_ty_vars = List.fold_left add_ty_var
let add_term_vars = List.fold_left add_term_var

let add_ty_sk env vars (ty_args, t_args) =
  assert (t_args = []);
  let ty_args = List.map (Expr.Ty.subst env.type_vars Expr.Subst.empty) ty_args in
  { env with type_vars = List.fold_left (fun s v ->
        Expr.Subst.Id.bind s v (Expr.Ty.apply (Expr.Id.ty_skolem v) ty_args)
      ) env.type_vars vars }

let add_term_sk env vars (ty_args, t_args) =
  let ty_args = List.map (Expr.Ty.subst env.type_vars Expr.Subst.empty) ty_args in
  let t_args = List.map (apply env) t_args in
  { env with term_vars = List.fold_left (fun s v ->
        Expr.Subst.Id.bind s v (Expr.Term.apply (Expr.Id.term_skolem v) ty_args t_args)
      ) env.term_vars vars }

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

  (* Util.debug ~sectionical connectives *)
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
  | { Expr.formula = Expr.All ((tys, ts), args, p) } ->
    let env' =
      if env.truth then begin
        let tmp = add_ty_vars env tys in
        add_term_vars tmp ts
      end else begin
        let tmp = add_ty_sk env tys args in
        add_term_sk tmp ts args
      end
    in
    specialize env' p
  | { Expr.formula = Expr.Ex ((tys, ts), args, p) } ->
    let env' =
      if not env.truth then begin
        let tmp = add_ty_vars env tys in
        add_term_vars tmp ts
      end else begin
        let tmp = add_ty_sk env tys args in
        add_term_sk tmp ts args
      end
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
    Util.debug ~section "@[<hov 2>generalizing:@ %a@\nFree_vars :@ %a%a@]"
         Expr.Print.formula f
           CCFormat.(list ~sep:(return "") (fun fmt v ->
               Format.fprintf fmt "|- %a" Expr.Print.id_ttype v)) ty_vars
           CCFormat.(list ~sep:(return "") (fun fmt v ->
               Format.fprintf fmt "|- %a" Expr.Print.id_ty v)) t_vars;
    Expr.Formula.all (ty_vars, t_vars) f

let prenex = function f -> generalize (specialize empty_env f)

(* Extension registering *)
(* ************************************************************************ *)

let do_formula f =
  let f' = prenex f in
  Util.debug ~section "input: %a" Expr.Print.formula f;
  if Expr.Formula.equal f f' then begin
    Util.debug ~section "output: not changed.";
    None
  end else begin
    Util.debug ~section "output: %a" Expr.Print.formula f';
    Some (f', Dispatcher.mk_proof "prenex" "pre" (Prenex TODO))
  end

let register () =
  Dispatcher.Plugin.register "prenex"
    ~descr:"Pre-process formulas to put them in prenex normal form" (
    Dispatcher.mk_ext
      ~section
      ~preprocess:do_formula
      ()
  )
