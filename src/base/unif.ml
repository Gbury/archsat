
(* Unification module *)

(* WARNING : In our case,
 * what are usually called 'variables' in litterature are
 * actually the metavariables in the terms *)

exception Not_unifiable of Expr.term * Expr.term

(* Metavariable protection *)
(* ************************************************************************ *)

let rec protect_term = function
    | { Expr.term = Expr.Meta m } -> Expr.term_of_meta (Expr.protect m)
    | { Expr.term = Expr.App (f, ty_l, t_l) } ->
      Expr.term_app f ty_l (List.map protect_term t_l)
    | t -> t

(* Metavariables substitutions *)
(* ************************************************************************ *)

module S = struct
    module M = Map.Make(struct
        type t = Expr.ty Expr.meta
        let compare = Expr.Meta.compare
    end)
    type t = Expr.term M.t
    let empty = M.empty

    let follow subst = function
      | { Expr.term = Expr.Meta m } -> M.find m subst
      | _ -> raise Not_found

    let bind m t subst = M.add m t subst

    let bindings = M.bindings

    let hash s = M.fold (fun m v h ->
        Hashtbl.hash (h, Expr.Meta.hash m, Expr.Term.hash v)) s 1

    let compare = M.compare Expr.Term.compare

    let equal = M.equal Expr.Term.equal
end

(* Robinson unification *)
(* ************************************************************************ *)

let rec occurs_check subst v = function
    | { Expr.term = Expr.Meta _ } as v' ->
      begin try
          occurs_check subst v (S.follow subst v')
      with Not_found ->
          Expr.Term.equal v v'
      end
    | { Expr.term= Expr.App (f, _, l) } -> List.exists (occurs_check subst v) l
    | _ -> false

let rec robinson subst s t =
    try robinson subst (S.follow subst s) t with Not_found ->
    try robinson subst s (S.follow subst t) with Not_found ->
      begin match s, t with
        | _ when Expr.Term.equal s t -> subst
        | ({ Expr.term = Expr.Meta ({Expr.can_unify= true} as v) } as m), u
        | u, ({ Expr.term = Expr.Meta ({Expr.can_unify = true} as v) } as m) ->
          if occurs_check subst m u then
            raise (Not_unifiable (m, u))
          else
            S.bind v u subst
        | { Expr.term = Expr.App (f, _, f_args) },
          { Expr.term = Expr.App (g, _, g_args) } ->
          if Expr.Var.equal f g then
            List.fold_left2 robinson subst f_args g_args
          else
            raise (Not_unifiable (s, t))
        | _ -> raise (Not_unifiable (s, t))
      end

let unify_simple s t = robinson S.empty s t

(* Caching *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Term)

let cache = H.create 1007

let cached_unify s t =
  let key = Builtin.tuple [s; t] in
  try
      H.find cache key
  with Not_found ->
      let res = unify_simple s t in
      H.add cache key res;
      res

