
(** Random generation of expressions

    This module is designed to generate random terms. Since truly random terms might
    not be that useful we instead constrain generated terms to live inside a specific
    signature of types and terms (defined in the [S] module).
*)

open Misc_test.Infix

(* Small matching algorithm for types *)
(* ************************************************************************ *)

module Match = struct

  exception No_match

  let rec ty_aux subst pat ty =
    let open Expr in
    match pat, ty with
    | { ty = TyVar v }, _ ->
      begin match Expr.Subst.Id.get v subst with
        | t ->
          if Expr.Ty.equal t ty then subst else raise No_match
        | exception Not_found ->
          Expr.Subst.Id.bind subst v ty
      end
    | { ty = TyApp (id, l) }, { ty = TyApp (id', l') } ->
      if Expr.Id.equal id id' then
        List.fold_left2 ty_aux subst l l'
      else
        raise No_match
    | _ -> raise No_match

  let ty pat ty =
    try
      let res = ty_aux Expr.Subst.empty pat ty in
      Some res
    with No_match ->
      None
end


(* Identifiers used in random terms *)
(* ************************************************************************ *)


module C = struct

  (** Types *)
  let type_a_id = Expr.Id.ty_fun "a" 0
  let type_b_id = Expr.Id.ty_fun "b" 0
  let type_list_id = Expr.Id.ty_fun "list" 1
  let type_pair_id = Expr.Id.ty_fun "pair" 2

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

(* Type generation *)
(* ************************************************************************ *)

module Ty = struct

  let print ty =
    Format.asprintf "%a" Expr.Ty.print ty

  let small =
    let rec aux acc = function
    | { Expr.ty = Expr.TyVar _ }
    | { Expr.ty = Expr.TyMeta _ } -> acc + 1
    | { Expr.ty = Expr.TyApp(_, l) } ->
      List.fold_left aux (acc + 1) l
    in
    aux 0

  let shrink = function
    | { Expr.ty = Expr.TyVar _ }
    | { Expr.ty = Expr.TyMeta _ } -> I.empty
    | { Expr.ty = Expr.TyApp(_, l) } -> I.of_list l

  let sized =
    let base = G.oneofl [ C.type_a; C.type_b; C.type_prop; ] in
    G.fix (fun self n ->
        if n = 0 then base
        else begin
          G.frequency [
            3, base;
            1, G.(return C.mk_list_type <*> self (n-1));
            1, G.(return C.mk_pair_type <*> self (n-1) <*> self (n-1));
          ]
        end
      )

  let gen = G.sized sized

  let make g = QCheck.make ~print ~small ~shrink g

  let t = make gen

end

(* Variable generation *)
(* ************************************************************************ *)

module Var = struct

  module H = Hashtbl.Make(Expr.Ty)

  let num = 10
  let table = H.create 42

  let get ty =
    try H.find table ty
    with Not_found ->
      let a = Array.init num (fun i ->
          Expr.Id.ty (Format.sprintf "v%d" i) ty) in
      H.add table ty a;
      a

  let gen ty =
    G.map (fun i -> (get ty).(i)) G.(0 -- (num - 1))

end

(* Meta-variable generation *)
(* ************************************************************************ *)

module Meta = struct

  module H = Hashtbl.Make(Expr.Ty)

  let num = 10
  let table = H.create 42

  let get ty =
    try H.find table ty
    with Not_found ->
      let a = Array.init num (fun i ->
          let v = Expr.Id.ty (Format.sprintf "m%d" i) ty in
          match Expr.(Meta.of_all (Formula.(all [v] f_true))) with
          | [ m ] -> m
          | _ -> assert false
        ) in
      H.add table ty a;
      a

  let gen ty =
    G.map (fun i -> (get ty).(i)) G.(0 -- (num - 1))

end

(* Term generation *)
(* ************************************************************************ *)

module Term = struct

  let consts = C.[
      a_0; a_1; a_2; b_0; b_1; b_2;
      f_a; g_a; h_a; f_b; g_b; h_b;
      p_0; p_1; p_2; f_p; g_p; h_p;
      pair; nil; cons;
    ]

  let print t =
    Format.asprintf "%a" Expr.Term.print t

  let small =
    let rec aux acc = function
      | { Expr.term = Expr.Var _ }
      | { Expr.term = Expr.Meta _ } -> acc + 1
      | { Expr.term = Expr.App(_, _, l) } ->
        List.fold_left aux (acc + 1) l
    in
    aux 0

  let rec sub = function
    | { Expr.term = Expr.Var _ }
    | { Expr.term = Expr.Meta _ } -> I.empty
    | { Expr.term = Expr.App(_, _, l) } ->
      let i = I.of_list l in
      I.(append i (i >>= sub))

  let shrink term =
    let aux t = Expr.(Ty.equal term.t_type t.t_type) in
    Misc_test.iter_filter aux (sub term)

  type config = {
    var : int;
    meta : int;
  }

  let ground = { var = 0; meta = 1; }

  let rec typed ~config ty size =
    (** This is used to filter constant that can produce a term
        of the required type [ty]. *)
    let aux c =
      match Match.ty Expr.(c.id_type.fun_ret) ty with
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
    assert (l3 <> []);
    (** Finally, insert the possibility to generate a variable when we want to
        generate a leaf (i.e ground is true, and size <= 1). *)
    let l4 =
      if size > 1 then l3
      else (config.var, `Var) :: (config.meta, `Meta) :: l3
    in
    (** Turn the possibility list into a generator. *)
    G.(frequencyl l4 >>= (fun x ->
        match x with
        | `Var -> Var.gen ty >|= Expr.Term.of_id
        | `Meta -> Meta.gen ty >|= Expr.Term.of_meta
        | `Cst (c, subst) ->
          let tys = List.map (fun v -> Expr.Subst.Id.get v subst) Expr.(c.id_type.fun_vars) in
          let args = List.map (Expr.Ty.subst subst) Expr.(c.id_type.fun_args) in
          Misc_test.split (max 0 (size - 1)) (List.length args) >>= fun sizes ->
          sized_list ~config args sizes >|= (Expr.Term.apply c tys)
      ))

  and sized_list ~config l sizes =
    match l, sizes with
    | [], [] -> G.return []
    | ty :: r, size :: rest ->
      G.(typed ~config ty size >>= fun t ->
         sized_list ~config r rest >|= fun tail ->
         t :: tail)
    | _ -> assert false

  let sized size =
    G.(Ty.gen >>= fun ty -> typed ~config:ground ty size)

  let gen = G.sized sized

  let make g = QCheck.make ~print ~small ~shrink g

  let t = make gen

end


(* Formula generation *)
(* ************************************************************************ *)

module Formula = struct

  let print f =
    Format.asprintf "%a" Expr.Formula.print f

  let small =
    let rec aux acc = function
      | { Expr.formula = Expr.True }
      | { Expr.formula = Expr.False } ->
        acc + 1
      | { Expr.formula = Expr.Pred t } ->
        acc + Term.small t
      | { Expr.formula = Expr.Equal (a, b) } ->
        acc + Term.small a + Term.small b
      | { Expr.formula = Expr.Not p } ->
        aux (acc + 1) p
      | { Expr.formula = Expr.Or l }
      | { Expr.formula = Expr.And l } ->
        List.fold_left aux (acc + 1) l
      | { Expr.formula = Expr.Imply (p, q) }
      | { Expr.formula = Expr.Equiv (p, q) } ->
        aux (aux (acc + 1) p) q
      | { Expr.formula = Expr.Ex (l, _, p) }
      | { Expr.formula = Expr.All (l, _, p) } ->
        aux (acc + List.length l) p
      | { Expr.formula = Expr.ExTy (l, _, p) }
      | { Expr.formula = Expr.AllTy (l, _, p) } ->
        aux (acc + List.length l) p
    in
    aux 0

  let rec shrink = function
    | { Expr.formula = Expr.True }
    | { Expr.formula = Expr.False } ->
      I.empty
    | { Expr.formula = Expr.Not p } ->
      I.return p
    | { Expr.formula = Expr.Pred t } ->
      I.map Expr.Formula.pred (Term.shrink t)
    | { Expr.formula = Expr.Equal (a, b) } ->
      I.(pair (Term.shrink a) (Term.shrink b)
         >|= fun (x, y) -> Expr.Formula.eq x y)
    | { Expr.formula = Expr.Or l } ->
      I.(append (of_list l)
           (S.list ~shrink l >|= Expr.Formula.f_or))
    | { Expr.formula = Expr.And l } ->
      I.(append (of_list l)
           (S.list ~shrink l >|= Expr.Formula.f_and))
    | { Expr.formula = Expr.Imply (p, q) } ->
      I.(pair (shrink p) (shrink q)
         >|= fun (x, y) -> Expr.Formula.imply x y)
    | { Expr.formula = Expr.Equiv (p, q) } ->
      I.(pair (shrink p) (shrink q)
         >|= fun (x, y) -> Expr.Formula.equiv x y)
    | { Expr.formula = Expr.Ex (l, _, p) } ->
      I.(shrink p >|= fun q ->
         let _, vars = Expr.Formula.fv q in
         let l' = List.filter (fun x ->
             List.exists (Expr.Id.equal x) vars) l in
         Expr.Formula.ex l' q)
    | { Expr.formula = Expr.All (l, _, p) } ->
      I.(shrink p >|= fun q ->
         let _, vars = Expr.Formula.fv q in
         let l' = List.filter (fun x ->
             List.exists (Expr.Id.equal x) vars) l in
         Expr.Formula.all l' q)
    | { Expr.formula = Expr.ExTy (l, _, p) } ->
      I.(shrink p >|= fun q ->
         let vars, _ = Expr.Formula.fv q in
         let l' = List.filter (fun x ->
             List.exists (Expr.Id.equal x) vars) l in
         Expr.Formula.exty l' q)
    | { Expr.formula = Expr.AllTy (l, _, p) } ->
      I.(shrink p >|= fun q ->
         let vars, _ = Expr.Formula.fv q in
         let l' = List.filter (fun x ->
             List.exists (Expr.Id.equal x) vars) l in
         Expr.Formula.allty l' q)

  type config = {
    term  : Term.config;
    eq    : int;
    pred  : int;
    neg   : int;
    conj  : int;
    disj  : int;
    impl  : int;
    equiv : int;
    all   : int;
    allty : int;
    ex    : int;
    exty  : int;
  }

  let default = {
    term = Term.({ var = 1; meta = 0; });
    eq    = 3;
    pred  = 4;
    neg   = 1;
    conj  = 1;
    disj  = 1;
    impl  = 1;
    equiv = 1;
    all   = 1;
    allty = 1;
    ex    = 1;
    exty  = 1;
  }

  let pred ~config size =
    G.(return Expr.Formula.pred <*>
       (Term.typed ~config:config.term Expr.Ty.prop size))

  let eq ~config size =
    G.(Misc_test.split_int size >>= fun (a, b) ->
       Ty.sized (min 5 size) >>= fun ty ->
       return Expr.Formula.eq
       <*> (Term.typed ~config:config.term ty a)
       <*> (Term.typed ~config:config.term ty b)
      )

  let all f =
    let _, vars = Expr.Formula.fv f in
    G.(Misc_test.sublist vars >|= fun l ->
       Expr.Formula.all l f)

  let ex f =
    let _, vars = Expr.Formula.fv f in
    G.(Misc_test.sublist vars >|= fun l ->
       Expr.Formula.ex l f)

  let allty f =
    let vars, _ = Expr.Formula.fv f in
    G.(Misc_test.sublist vars >|= fun l ->
       Expr.Formula.allty l f)

  let exty f =
    let vars, _ = Expr.Formula.fv f in
    G.(Misc_test.sublist vars >|= fun l ->
       Expr.Formula.exty l f)

  let guided ~config =
    G.fix (fun self n ->
        if n = 0 then
          G.frequency [
            1, G.return Expr.Formula.f_true;
            1, G.return Expr.Formula.f_false;
          ]
        else
          G.frequency [
            config.eq,    eq ~config n;
            config.pred,  pred ~config n;
            config.ex,    G.(self (n-1) >>= ex);
            config.all,   G.(self (n-1) >>= all);
            config.exty,  G.(self (n-1) >>= exty);
            config.allty, G.(self (n-1) >>= allty);
            config.neg,   G.(return Expr.Formula.neg <*> self (n-1));
            config.conj,  G.(Misc_test.split_int (n-1) >>= fun (a, b) ->
                             self a >>= fun p -> self b >>= fun q ->
                             return @@ Expr.Formula.f_and [p; q]);
            config.disj,  G.(Misc_test.split_int (n-1) >>= fun (a, b) ->
                             self a >>= fun p -> self b >>= fun q ->
                             return @@ Expr.Formula.f_or [p; q]);
            config.impl,  G.(Misc_test.split_int (n-1) >>= fun (a, b) ->
                             return Expr.Formula.imply <*> self a <*> self b);
            config.equiv, G.(Misc_test.split_int (n-1) >>= fun (a, b) ->
                             return Expr.Formula.equiv <*> self a <*> self b);
          ]
      )

  let closed ~config size =
    G.(guided ~config size >|= (fun f ->
        let tys, vars = Expr.Formula.fv f in
        Expr.Formula.allty tys (Expr.Formula.all vars f)))

  let sized = closed ~config:default

  let gen = G.sized sized

  let make g = QCheck.make ~print ~small ~shrink g

  let t = make gen

  let meta f =
    let tys, l = Expr.Formula.fv f in
    assert (tys = []);
    match Expr.Formula.all l f with
    | { Expr.formula = Expr.All (vars, _, _) } as q_f ->
      let metas = List.map Expr.Term.of_meta (Expr.Meta.of_all q_f) in
      let subst = List.fold_left2 Expr.Subst.Id.bind Expr.Subst.empty vars metas in
      Expr.Formula.subst Expr.Subst.empty subst f
    | _ -> f

  let meta_tt (u, v) =
    assert Expr.(Ty.equal u.t_type v.t_type);
    let eq = Expr.Formula.eq u v in
    match meta eq with
    | { Expr.formula = Expr.Equal (t, t') }
    | { Expr.formula = Expr.Equiv (
            { Expr.formula = Expr.Pred t},
            { Expr.formula = Expr.Pred t'} ) } ->
      (t, t')
    | _ -> assert false

end

