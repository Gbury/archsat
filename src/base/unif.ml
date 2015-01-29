
(* Unification module *)

(* WARNING : In our case,
 * what are usually called 'variables' in litterature are
 * actually the metavariables in the terms *)

exception Not_unifiable

(* Metavariables substitutions *)
(* ************************************************************************ *)

module M = Map.Make(struct
    type t = Expr.ty Expr.meta
    let compare m1 m2 = Expr.(Var.compare m1.meta_var m2.meta_var)
end)

type subst = Expr.term M.t

let empty = M.empty

let follow subst = function
    | { Expr.term = Expr.Meta m } -> M.find m subst
    | _ -> raise Not_found

let bind m t subst = M.add m t subst

let bindings = M.bindings

(* Robinson unification *)
(* ************************************************************************ *)

let rec occurs_check subst v = function
    | { Expr.term = Expr.Meta _ } as v' ->
      begin try
          occurs_check subst v (follow subst v')
      with Not_found ->
          Expr.Term.equal v v'
      end
    | { Expr.term= Expr.App (f, _, l) } -> List.exists (occurs_check subst v) l
    | _ -> false

let rec robinson subst s t =
    try robinson subst (follow subst s) t with Not_found ->
    try robinson subst s (follow subst t) with Not_found ->
      begin match s, t with
        | ({ Expr.term = Expr.Meta v } as m), u
        | u, ({ Expr.term = Expr.Meta v } as m) ->
          if Expr.Term.equal s t then
            subst
          else if occurs_check subst m u then
            raise Not_unifiable
          else
            bind v u subst
        | { Expr.term = Expr.App (f, _, f_args) },
          { Expr.term = Expr.App (g, _, g_args) } ->
          if Expr.Var.equal f g then
            List.fold_left2 robinson subst f_args g_args
          else
            raise Not_unifiable
        | _ -> raise Not_unifiable
      end

let unify_simple s t = robinson empty s t

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

