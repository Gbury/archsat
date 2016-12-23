
(** Random generation of terms

    This module is designed to generate random terms. Since truly random terms might
    not be that useful we instead constrain generated terms to live inside a specific
    signature of types and terms (defined in the [S] module).
*)

let section = Util.Section.make "Random"

(* Small matching algorithm for types *)
(* ************************************************************************ *)

exception No_match

let rec match_ty_aux subst pat ty =
  let open Expr in
  match pat, ty with
  | { ty = TyVar v }, _ ->
    begin match Expr.Subst.Id.get v subst with
      | t ->
        if Expr.Ty.equal t ty then subst else raise No_match
      | exception Not_found ->
        Expr.Subst.Id.bind v ty subst
    end
  | { ty = TyApp (id, l) }, { ty = TyApp (id', l') } ->
    if Expr.Id.equal id id' then
      List.fold_left2 match_ty_aux subst l l'
    else
      raise No_match
  | _ -> raise No_match

let match_ty pat ty =
  try
    let res = match_ty_aux Expr.Subst.empty pat ty in
    Some res
  with No_match ->
    None

(* Identifiers used in random terms *)
(* ************************************************************************ *)


module S = struct

  (** Types *)
  let type_a_id = Expr.Id.ty_fun "a" 0
  let type_b_id = Expr.Id.ty_fun "b" 0
  let type_list_id = Expr.Id.ty_fun "list" 1
  let type_pair_id = Expr.Id.ty_fun "pair" 2

  let type_base = Expr.Ty.base
  let type_prop = Expr.Ty.prop
  let type_a = Expr.Ty.apply type_a_id []
  let type_b = Expr.Ty.apply type_b_id []
  let mk_list_type a = Expr.Ty.apply type_list_id [a]
  let mk_pair_type a b = Expr.Ty.apply type_pair_id [a; b]

  (** Constants *)
  let a_0 = Expr.Id.term_fun "a_0" [] [] type_a
  let a_1 = Expr.Id.term_fun "a_1" [] [] type_a
  let a_2 = Expr.Id.term_fun "a_2" [] [] type_a

  let f_a = Expr.Id.term_fun "f_a" [] [ type_a ] type_a
  let g_a = Expr.Id.term_fun "g_a" [] [ type_a; type_b] type_a
  let h_a = Expr.Id.term_fun "h_a" [] [ mk_list_type type_a ] type_a

  let b_0 = Expr.Id.term_fun "b_0" [] [] type_b
  let b_1 = Expr.Id.term_fun "b_1" [] [] type_b
  let b_2 = Expr.Id.term_fun "b_2" [] [] type_b

  let f_b = Expr.Id.term_fun "f_b" [] [ type_b ] type_b
  let g_b = Expr.Id.term_fun "g_b" [] [ type_b; type_a ] type_b
  let h_b = Expr.Id.term_fun "h_b" [] [ mk_pair_type type_a type_b ] type_b

  let p_0 = Expr.Id.term_fun "p_0" [] [] type_prop
  let p_1 = Expr.Id.term_fun "p_1" [] [] type_prop
  let p_2 = Expr.Id.term_fun "p_2" [] [] type_prop

  let f_p = Expr.Id.term_fun "f_p" [] [type_a; type_b] type_prop
  let g_p = Expr.Id.term_fun "g_p" [] [mk_list_type type_a] type_prop
  let h_p = Expr.Id.term_fun "h_p" [] [mk_pair_type type_b type_a] type_prop

  let pair =
    let a = Expr.Id.ttype "alpha" in
    let b = Expr.Id.ttype "beta" in
    let t_a = Expr.Ty.of_id a in
    let t_b = Expr.Ty.of_id b in
    Expr.Id.term_fun "pair" [a; b] [t_a; t_b] (mk_pair_type t_a t_b)

  let nil =
    let a = Expr.Id.ttype "alpha" in
    let t_a = Expr.Ty.of_id a in
    Expr.Id.term_fun "nil" [a] [] (mk_list_type t_a)

  let cons =
    let a = Expr.Id.ttype "alpha" in
    let t_a = Expr.Ty.of_id a in
    Expr.Id.term_fun "cons" [a] [t_a; mk_list_type t_a] (mk_list_type t_a)

end

(* Convenience functions *)
(* ************************************************************************ *)

module G = QCheck.Gen

let sized g = G.(3 -- 50 >>= g)

let rec split size len =
  let open G in
  if len = 0 then
    return []
  else if len = 1 then
    return [size]
  else begin
    (0 -- size) >>= fun hd ->
    split (size - hd) (len - 1) >|= fun tl ->
    hd :: tl
  end

let split_int size =
  G.(split size 2 >|= function
    | [a; b] -> a, b | _ -> assert false)

(* Type generation *)
(* ************************************************************************ *)

let ty =
  let base = G.oneofl [ S.type_a; S.type_b; S.type_prop; ] in
  G.fix (fun self n ->
      if n = 0 then base
      else begin
        G.frequency [
          3, base;
          1, G.(return S.mk_list_type <*> self (n-1));
          1, G.(return S.mk_pair_type <*> self (n-1) <*> self (n-1));
        ]
      end
    )

(* Variable generation *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Ty)

let var_num = 10
let var_table = H.create 42

let get_vars ty =
  try H.find var_table ty
  with Not_found ->
    let a = Array.init var_num (fun i ->
        Expr.Id.ty (Format.sprintf "v%d" i) ty) in
    H.add var_table ty a;
    a

let var ty =
  G.map (fun i -> (get_vars ty).(i)) G.(0 -- (var_num - 1))

(* Term generation *)
(* ************************************************************************ *)

let consts = S.[
    a_0; a_1; a_2; b_0; b_1; b_2;
    f_a; g_a; h_a; f_b; g_b; h_b;
    p_0; p_1; p_2; f_p; g_p; h_p;
    pair; nil; cons;
  ]

let rec term_aux ?(ground=true) size ty =
  (** This is used to filter constant that can produce a term
      of the required type [ty]. *)
  let aux c =
    match match_ty Expr.(c.id_type.fun_ret) ty with
    | None -> None
    | Some subst -> Some (c, subst)
  in
  (** This is used to filter constants base on their arity. Only
      constants with arity > 0 should be considered when [size > 1]. *)
  let score (c, subst) =
    if (size <= 1) then begin
      if List.length Expr.(c.id_type.fun_args) = 0 then
        Some (1, `Cst (c, subst))
      else
        None
    end else begin
      if List.length Expr.(c.id_type.fun_args) > 0 then
        Some (1, `Cst (c, subst))
      else
        None
    end
  in
  (** Apply the above functions *)
  let l1 = CCList.filter_map aux consts in
  assert (l1 <> []);
  let l2 = CCList.filter_map score l1 in
  (** Check wether the last filter was too restrictive. For instance, if [size=0),
      and we need to generate a pair, then the only constructor will ahve arity > 0,
      and thus we need to get it back. *)
  let l3 =
    if l2 <> [] then l2
    else begin
      List.map (fun x -> (1, `Cst x)) l1
    end
  in
  (** Finally, insert the possibility to generate a variable when we want to
      generate a leaf (i.e ground is true, and size <= 1). *)
  let l4 =
    if ground || size > 1 then l3
    else (2, `Var) :: l3
  in
  assert (l4 <> [] && List.for_all (fun (n, _) -> n > 0) l4);
  (** Turn the possibility list into a generator. *)
  G.(frequencyl l4 >>= (fun x ->
      match x with
      | `Var -> var ty >|= Expr.Term.of_id
      | `Cst (c, subst) ->
        let tys = List.map (fun v -> Expr.Subst.Id.get v subst) Expr.(c.id_type.fun_vars) in
        let args = List.map (Expr.Ty.subst subst) Expr.(c.id_type.fun_args) in
        split (max 0 (size - 1)) (List.length args) >>= fun sizes ->
        term_list ~ground sizes args >|= (Expr.Term.apply c tys)
    ))

and term_list ~ground sizes l =
  match sizes, l with
  | [], [] -> G.return []
  | size :: rest, ty :: r ->
    G.(term_aux ~ground size ty >>= fun t ->
       term_list ~ground rest r >|= fun tail ->
       t :: tail)
  | _ -> assert false

let term ~ground size =
  G.(ty (min 5 size) >>= term_aux ~ground size)

(* Formula generation for unification poblems *)
(* ************************************************************************ *)

let pred ~ground size =
  G.(return Expr.Formula.pred <*> (term_aux ~ground size Expr.Ty.prop))

let eq ~ground size =
  G.(split_int size >>= fun (a, b) ->
     ty (min 5 size) >>= fun ty ->
     return Expr.Formula.eq
     <*> (term_aux ~ground a ty)
     <*> (term_aux ~ground b ty)
    )

let meta gen size =
  G.(gen ~ground:false size >|= fun f ->
     let tys, l = Expr.Formula.fv f in
     assert (tys = []);
     match Expr.Formula.all l f with
     | { Expr.formula = Expr.All (vars, _, _) } as q_f ->
       let metas = List.map Expr.Term.of_meta (Expr.Meta.of_all q_f) in
       let subst = List.fold_left2 (fun s v t -> Expr.Subst.Id.bind v t s)
           Expr.Subst.empty vars metas in
       Expr.Formula.subst Expr.Subst.empty subst f
     | _ -> f)


