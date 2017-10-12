
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

module Ctx = struct

  exception Added_twice of Expr.formula
  exception Not_introduced of Expr.formula

  let () =
    Printexc.register_printer (function
        | Added_twice f ->
          Some (Format.asprintf
                  "Following formula has been adde twice to context:@ %a"
                  Expr.Print.formula f)
        | Not_introduced f ->
          Some (Format.asprintf
                  "Following formula is used in a context where it is not declared:@ %a"
                  Expr.Print.formula f)
        | _ -> None
      )


  module Hf = Hashtbl.Make(Expr.Formula)

  type wrapper = (Format.formatter -> unit -> unit) ->
    Format.formatter -> (Expr.formula * Expr.formula) -> unit

  type t = {
    (** Prefixed formula name map *)
    prefix : string;
    wrapper : wrapper;
    mutable count : int;
    names : (Expr.formula * string) Hf.t;
  }

  let _wrap pp fmt _ = pp fmt ()

  let mk ?(wrapper=_wrap) ~prefix = {
    prefix; wrapper;
    count = 0; names = Hf.create 13;
  }

  (* Named formulas with a prefix. *)
  let find t f =
    try Hf.find t.names f
    with Not_found -> raise (Not_introduced f)

  let new_name t =
    let () = t.count <- t.count + 1 in
    Format.sprintf "%s%d" t.prefix t.count

  let add_aux t f g =
    match Hf.find t.names f with
    | (f', name) -> raise (Added_twice f')
    | exception Not_found ->
      let name = g t in
      let res = (f, name) in
      Hf.add t.names f res;
      name

  let add_force t f name =
    ignore (add_aux t f (fun _ -> name))

  (* Printing *)
  let named t fmt f =
    let (f', name) = find t f in
    t.wrapper CCFormat.(const string name) fmt (f, f')

  let intro t fmt f =
    Format.fprintf fmt "%s" (add_aux t f new_name)

  (* Wrappers *)
  let add t f = ignore (add_aux t f new_name)
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
    | Fun of Expr.formula Expr.id list * t
    | App of Id.t * t list

end

(* Proof Tactics *)
(* ************************************************************************ *)

module Tactic = struct

  type t =
    | Intro of string list
    | Apply of Id.t

end

