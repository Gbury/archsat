
(* Log&Module Init *)
(* ************************************************************************ *)

let section = Section.make "synth"

module V = Hashtbl.Make(Expr.Id.TyCstr)
module H = Hashtbl.Make(Expr.Ty)
module S = Set.Make(Expr.Id.Const)
module T = Set.Make(Expr.Ty)

(* Helper functions *)
(* ************************************************************************ *)

let size term =
  let rec aux acc = function
    | { Expr.term = Expr.Var _ }
    | { Expr.term = Expr.Meta _ } -> 1
    | { Expr.term = Expr.App (_, _, l) } ->
      List.fold_left aux (acc + 1) l
  in
  aux 0 term

(* Association tables *)
(* ************************************************************************ *)

let poly_list = ref []
let head_table = V.create 1013

let get_head f =
  try V.find head_table f
  with Not_found -> S.empty

let add_head f v =
  let s = get_head f in
  V.add head_table f (S.add v s)

let add_id v =
  Util.debug ~section "Adding: %a" Expr.Print.const_ty v;
  match Expr.(v.id_type.fun_ret) with
  | { Expr.ty = Expr.TyMeta _ } -> assert false
  | { Expr.ty = Expr.TyVar _ } -> poly_list := v :: !poly_list
  | { Expr.ty = Expr.TyApp (f, _) } -> add_head f v

let iter_on_head h =
  let s = get_head h in
  let l = !poly_list in
  (fun f ->
     let () = S.iter f s in
     List.iter f l
  )

(* Synthetizing functions *)
(* ************************************************************************ *)

let table = H.create 1013

let rec term_try s ty v =
  match Match.ty Mapping.empty Expr.(v.id_type.fun_ret) ty with
  | exception Match.Impossible_ty _ -> None
  | m ->
    assert (List.for_all (Mapping.Var.mem_ty m) Expr.(v.id_type.fun_vars));
    let tys = List.map (Mapping.Var.get_ty m) Expr.(v.id_type.fun_vars) in
    let arg_tys = List.map (Mapping.apply_ty m) Expr.(v.id_type.fun_args) in
    CCOpt.map (Expr.Term.apply v tys) @@
    CCOpt.sequence_l (List.map (find_term s) arg_tys)

and term_aux s = function
  | { Expr.ty = Expr.TyVar _ } -> assert false
  | { Expr.ty = Expr.TyMeta _ } -> find_term s Expr.Ty.base
  | { Expr.ty = Expr.TyApp (f, _) } as ty ->
    CCFun.(
      iter_on_head f
      |> Sequence.filter_map (term_try s ty)
      |> Sequence.map (fun t -> size t, t)
      |> Sequence.min ~lt:(fun (i, _) (j, _) -> i < j)
      |> CCOpt.map snd)

and find_term s ty =
  try Some (H.find table ty)
  with Not_found ->
    Util.debug ~section "Synthetizing term of type:@ %a" Expr.Print.ty ty;
    if T.mem ty s then None (** cyclic synthesis. TODO: better stopping criterion,
                                the current one is not enough if there are symbols
                                of type {'a list list -> 'a list} *)
    else CCOpt.map
        (fun res -> H.add table ty res; res)
        (term_aux (T.add ty s) ty)

(* API functions *)
(* ************************************************************************ *)

let ty = Expr.Ty.base

let term = Util.within_prof section (find_term T.empty)

let register term =
  let ty = Expr.(term.t_type) in
  assert (Expr.Ty.fv ty = ([], []));
  H.add table ty term

