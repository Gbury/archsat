
let section = Section.make "proof"

(* Global context *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Dolmen.Id)

(* mutable state *)
let goals = ref []
let hyp_table = H.create 1013

(* Wrapper functions *)
let add_hyp = H.add hyp_table

let find_hyp = H.find hyp_table

let add_goal id g =
  begin match !goals with
    | [] -> ()
    | _ -> Util.warn ~section "%s%s"
             "Multiple goals are not very well supported,@ "
             "please consider having a single goal at any time"
  end;
  add_hyp id [Expr.Formula.neg g];
  goals := (id, g) :: !goals

let get_goals () = !goals

let clear_goals () = goals := []

(* Proof contextx *)
(* ************************************************************************ *)

module Env = struct

  exception Added_twice of Expr.formula
  exception Not_introduced of Expr.formula

  let () =
    Printexc.register_printer (function
        | Added_twice f ->
          Some (Format.asprintf
                  "Following formula has been added twice to context:@ %a"
                  Expr.Print.formula f)
        | Not_introduced f ->
          Some (Format.asprintf
                  "Following formula is used in a context where it is not declared:@ %a"
                  Expr.Print.formula f)
        | _ -> None
      )


  module M = Map.Make(Expr.Formula)

  type wrapper = (Format.formatter -> unit -> unit) ->
    Format.formatter -> (Expr.formula * Expr.formula) -> unit

  type t = {
    (** Prefixed formula name map *)
    count : int;
    prefix : string;
    wrapper : wrapper;
    names : (Expr.formula * string) M.t;
  }

  let _wrap pp fmt _ = pp fmt ()

  let empty ?(wrapper=_wrap) ~prefix =
    { prefix; wrapper; count = 0; names = M.empty; }

  (* Named formulas with a prefix. *)
  let find t f =
    try M.find f t.names
    with Not_found -> raise (Not_introduced f)

  let new_name t =
    { t with count = t.count + 1 },
    Format.sprintf "%s%d" t.prefix t.count

  let intro t f =
    match M.find f t.names with
    | (f', name) -> raise (Added_twice f')
    | exception Not_found ->
      let t', name = new_name t in
      let res = (f, name) in
      let t'' = { t' with names = M.add f res t.names } in
      t'', name

  (* Printing *)
  let named t fmt f =
    let (f', name) = find t f in
    t.wrapper CCFormat.(const string name) fmt (f, f')

  (* Wrappers *)
  let name t f = Format.asprintf "%a" (named t) f

end

(* Proof constants *)
(* ************************************************************************ *)

module Id = struct

  type ('a, 'b) pi = 'a Expr.id option * 'b

  type 'a ty =
    | Ret     : 'a -> 'a ty
    | Pi_ty   : (Expr.ttype, Expr.ty) pi    * 'a ty -> 'a ty
    | Pi_term : (Expr.ty, Expr.term) pi     * 'a ty -> 'a ty
    | Pi_form : (Expr.ty, Expr.formula) pi  * 'a ty -> 'a ty

  type t = Expr.formula ty Expr.id

end

(* Proof terms *)
(* ************************************************************************ *)

module Term = struct

  type t =
    | Ty of Expr.ty
    | Term of Expr.term
    | Formula of Expr.formula
    | Fun of Expr.formula Expr.id list * t
    | App of Id.t * t list

end

(* Proof Tactics *)
(* ************************************************************************ *)

module Tactic = struct

  type 'a order =
    | Leaf of 'a
    | Node of ('a order) Expr.order

  type step =
    | Apply of Id.t * Term.t option list
    (** Application of a term, with possible holes. *)
    | Destruct of string option * (string * t) order
    (** Destruct the named formula (or the goal if [None]),
        and use the corresponding tactics. *)
  (** The type for tactic steps. *)

  and t = {
    env : Env.t;
    goal : Expr.formula;
    tactics : step list;
  }

  let intros () t =
    let rec aux acc env goal =
      match goal.Expr.formula with
      | Expr.Imply (p, q) ->
        let env', name = Env.intro env p in
        aux (name :: acc) env' q
      | _ -> List.rev acc, env, goal
    in
    let names, env, goal = aux [] t.env t.goal in
    { env; goal; tactics = Intro names :: t.tactics; }


end

