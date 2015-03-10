
(*
let log_section = Util.Section.make "inst"
let log i fmt = Util.debug ~section:log_section i fmt
*)

(* Instanciation helpers *)
let index m = Expr.(m.meta_index)

(* Partial order, representing the inclusion on quantified formulas
 * Uses the free variables to determine inclusion. *)
let free_args = function
  | { Expr.formula = Expr.All (_, args, _) }
  | { Expr.formula = Expr.Ex (_, args, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (_, args, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (_, args, _) } }
  | { Expr.formula = Expr.AllTy (_, args, _) }
  | { Expr.formula = Expr.ExTy (_, args, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (_, args, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (_, args, _) } } -> args
  | _ -> assert false

let sub_quant p q = match p with
  | { Expr.formula = Expr.All (l, _, _) }
  | { Expr.formula = Expr.Ex (l, _, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.All (l, _, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, _, _) } } ->
    let _, tl = free_args q in
    List.exists (fun v -> List.exists (function
        | { Expr.term = Expr.Var v' } | { Expr.term = Expr.Meta { Expr.meta_var = v' } } ->
          Expr.Var.equal v v'
        | _ -> false) tl) l
  | { Expr.formula = Expr.AllTy (l, _, _) }
  | { Expr.formula = Expr.ExTy (l, _, _) }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.AllTy (l, _, _) } }
  | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (l, _, _) } } ->
    let tyl, _ = free_args q in
    List.exists (fun v -> List.exists (function
        | { Expr.ty = Expr.TyVar v' } | { Expr.ty = Expr.TyMeta { Expr.meta_var = v' } } ->
          Expr.Var.equal v v'
        | _ -> false) tyl) l
  | _ -> assert false

let quant_compare p q =
  if Expr.Formula.equal p q then
      Some 0
  else if sub_quant p q then
      Some 1
  else if sub_quant q p then
      Some ~-1
  else
      None

let quant_comparable p q = match quant_compare p q with
  | Some _ -> true
  | None -> false

(* Splits an arbitrary unifier (Unif.t) into a list of
 * unifiers such that all formula generating the metas in
 * a unifier are comparable according to compare_quant. *)
let belong_ty m s =
    let f = Expr.get_meta_ty_def (index m) in
    let aux m' _ =
        let f' = Expr.get_meta_ty_def (index m') in
        if Expr.Formula.equal f f' then index m = index m'
        else quant_comparable f f'
    in
    Expr.Subst.exists aux Unif.(s.ty_map)

let belong_term m s =
    let f = Expr.get_meta_def (index m) in
    let aux m' _ =
        let f' = Expr.get_meta_def (index m') in
        if Expr.Formula.equal f f' then index m = index m'
        else quant_comparable f f'
    in
    Expr.Subst.exists aux Unif.(s.t_map)

let split s = [s]
(*
  let rec aux bind belongs acc m t = function
      | [] -> bind Unif.empty m t :: acc
      | s :: r ->
        if belongs m s then
          (bind s m t) :: (List.rev_append acc r)
        else
          aux bind belongs (s :: acc) m t r
  in
  Expr.Subst.fold (aux Unif.bind_term belong_term []) Unif.(s.t_map)
    (Expr.Subst.fold (aux Unif.bind_ty belong_ty []) Unif.(s.ty_map) [])
*)

(* Given an arbitrary substitution (Unif.t),
 * Returns a pair (formula * Unif.t) to instanciate
 * the outermost metas in the given unifier. *)
let partition s =
    let aux bind m t = function
        | None -> Some (index m, bind Unif.empty m t)
        | Some (min_index, acc) ->
          let i = index m in
          if i < min_index then
            Some (i, bind Unif.empty m t)
          else if i = min_index then
            Some (i, bind acc m t)
          else
            Some (min_index, acc)
    in
    match Expr.Subst.fold (aux Unif.bind_ty) Unif.(s.ty_map) None with
    | Some (i, u) -> Expr.get_meta_ty_def i, u
    | None ->
      match Expr.Subst.fold (aux Unif.bind_term) Unif.(s.t_map) None with
      | Some (i, u) -> Expr.get_meta_def i, u
      | None -> assert false

(* Produces a proof for the instanciation of the given formulas and unifiers *)
let mk_proof id f p s = Dispatcher.mk_proof
    ~ty_args:(Expr.Subst.fold (fun m t l -> Expr.type_meta m :: t :: l) Unif.(s.ty_map) [])
    ~term_args:(Expr.Subst.fold (fun m t l -> Expr.term_meta m :: t :: l) Unif.(s.t_map) [])
    ~formula_args:[f; p] id "inst"

let saturate u =
  let s_ty =
    try
      List.fold_left (fun s m -> Expr.Subst.Meta.bind m (Expr.type_meta (Expr.protect m)) s) Expr.Subst.empty
        (Expr.ty_metas_of_index (index (fst (Expr.Subst.choose Unif.(u.ty_map)))))
    with Not_found -> Expr.Subst.empty
  in
  let s_t =
    try
      List.fold_left (fun s m -> Expr.Subst.Meta.bind m (Expr.term_meta (Expr.protect m)) s) Expr.Subst.empty
        (Expr.term_metas_of_index (index (fst (Expr.Subst.choose Unif.(u.t_map)))))
    with Not_found -> Expr.Subst.empty
  in
  Unif.({
      ty_map = Expr.Subst.fold Expr.Subst.Meta.bind u.ty_map s_ty;
      t_map = Expr.Subst.fold Expr.Subst.Meta.bind u.t_map s_t;
  })

let to_var s = Expr.Subst.fold (fun {Expr.meta_var = v} t acc -> Expr.Subst.Var.bind v t acc) s Expr.Subst.empty

let hard_subst id f subst = match f with
  | { Expr.formula = Expr.All (_, _, p) } ->
    let u = saturate subst in
    let q = Expr.formula_subst Expr.Subst.empty (to_var Unif.(u.t_map)) p in
    [ Expr.f_not f; q], mk_proof id f q u
  | { Expr.formula = Expr.AllTy (_, _, p) } ->
    let u = saturate subst in
    let q = Expr.formula_subst (to_var Unif.(u.ty_map)) Expr.Subst.empty p in
    [ Expr.f_not f; q], mk_proof id f q u
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (_, _, p) } } ->
    let u = saturate subst in
    let q = Expr.formula_subst Expr.Subst.empty (to_var Unif.(u.t_map)) p in
    [ Expr.f_not f; Expr.f_not q], mk_proof id f q u
  | { Expr.formula = Expr.Not { Expr.formula = Expr.ExTy (_, _, p) } } ->
    let u = saturate subst in
    let q = Expr.formula_subst (to_var Unif.(u.ty_map)) Expr.Subst.empty p in
    [ Expr.f_not f; Expr.f_not q], mk_proof id f q u
  | _ -> assert false

let soft_subst id f subst =
  let q = Expr.partial_inst (to_var Unif.(subst.ty_map)) (to_var Unif.(subst.t_map)) f in
  [ Expr.f_not f; q], mk_proof id f q subst

(* Dispatcher extension part *)
let id = Dispatcher.new_id ()

let hard_push s =
  let (f, s) = partition s in
  let cl, p = hard_subst id f s in
  Dispatcher.push cl p

let soft_push s =
  let (f, s) = partition s in
  let cl, p = soft_subst id f s in
  Dispatcher.push cl p

;;
Dispatcher.(register {
    id = id;
    name = "inst";
    assume = (fun _ -> ());
    eval_pred = (fun _ -> None);
    preprocess = (fun _ -> ());
    if_sat = (fun _ -> ());
    options = (function t -> t);
    })

