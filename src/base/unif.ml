
(* Unification module *)

(* WARNING : In our case,
 * what are usually called 'variables' in litterature are
 * actually the metavariables in the terms *)

type subst = Expr.term_subst

exception Not_unifiable

(* Wrappers around substitutions *)
(* ************************************************************************ *)

let follow subst = function
    | { Expr.term = Expr.Meta { Expr.meta_var = v } } -> Expr.Subst.get v subst
    | _ -> raise Not_found

let bind m t subst = Expr.Subst.bind Expr.(m.meta_var) t subst

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
            Util.list_fold_product f_args g_args subst robinson
          else
            raise Not_unifiable
        | _ -> raise Not_unifiable
      end

let unify_simple s t = robinson Expr.Subst.empty s t


