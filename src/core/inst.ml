
let id = Dispatcher.new_id ()

let log_section = Util.Section.make "inst"
let log i fmt = Util.debug ~section:log_section i fmt

let print_inst l s =
  Expr.Subst.iter (fun k v -> log l " |- %a -> %a" Expr.debug_meta k Expr.debug_term v) Unif.(s.t_map)

(* Instanciation helpers *)
(* ************************************************************************ *)

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

let split s =
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

let simplify s = snd (partition s)

(* Produces a proof for the instanciation of the given formulas and unifiers *)
let mk_proof f p s = Dispatcher.mk_proof
    ~ty_args:(Expr.Subst.fold (fun m t l -> Expr.type_meta m :: t :: l) Unif.(s.ty_map) [])
    ~term_args:(Expr.Subst.fold (fun m t l -> Expr.term_meta m :: t :: l) Unif.(s.t_map) [])
    ~formula_args:[f; p] id "inst"

let to_var s = Expr.Subst.fold (fun {Expr.meta_var = v} t acc -> Expr.Subst.Var.bind v t acc) s Expr.Subst.empty

let soft_subst f subst =
  let q = Expr.partial_inst (to_var Unif.(subst.ty_map)) (to_var Unif.(subst.t_map)) f in
  [ Expr.f_not f; q], mk_proof f q subst

let soft_push s =
  let (f, s) = partition s in
  let cl, p = soft_subst f s in
  Dispatcher.push cl p

(* Heap for prioritizing instanciations *)
(* ************************************************************************ *)

module Inst = struct
  type t = {
    unif : Unif.t;
    score : int;
    age : int;
  }

  let age = ref 0
  let clock () = incr age

  let mk u k = {
    unif = u;
    score = k;
    age = !age;
  }

  let leq t1 t2 = t1.score + t1.age <= t2.score + t2.age
end

module Q = Heap.Make(Inst)
module H = Hashtbl.Make(Unif)

let heap = ref Q.empty
let inst_set = H.create 4096
let inst_incr = ref 3
let inst_done = ref 0

let get_u i = Inst.(i.unif)

let add ?(score=0) u =
  if not (H.mem inst_set u) then begin
    log 10 "New inst :";
    print_inst 10 u;
    H.add inst_set u false;
    heap := Q.add !heap (Inst.mk u score)
  end else
    log 10 "Redondant inst :";
  print_inst 10 u

let push inst =
  log 5 "Pushing inst :";
  incr inst_done;
  print_inst 5 (get_u inst);
  H.replace inst_set (get_u inst) true;
  soft_push (get_u inst)

let take f k =
  let aux f i =
    for _ = 1 to i do
      match Q.take !heap with
      | None -> ()
      | Some (new_h, min) ->
        heap := new_h;
        f min;
    done
  in
  if k > 0 then
    aux f k
  else
    aux f (Q.size !heap - k)

let inst_sat () =
  take push !inst_incr;
  Stats.register_msg "Instanciations done : %d" !inst_done;
  inst_done := 0;
  Inst.clock ()

(* Extension registering *)
(* ************************************************************************ *)

let opts t =
  let docs = Options.ext_sect in
  let n_of_inst =
    let doc = "Decides how many instanciations are pushed to the solver each round.
                   If $(docv) is a strictly positive number, then at each round, the $(docv)
                   most promising instanciations are pushed. If $(docv) is negative, then all
                   but the $(docv) least promising instanciations are pushed." in
    Cmdliner.Arg.(value & opt int 3 & info ["inst.nb"] ~docv:"N" ~docs ~doc)
  in
  let set_opts nb t =
    inst_incr := nb;
    t
  in
  Cmdliner.Term.(pure set_opts $ n_of_inst $ t)

;;
Dispatcher.(register (
    mk_ext
      ~prio:~-1 ~if_sat:inst_sat ~options:opts
      ~descr:"Handles the pushing of clauses corresponding to instanciations. This plugin does not
              do anything by itself, but rather is called by other plugins when doing instanciations.
              Activating it is not required for other plugins to use it."
      id "inst"
  ))

