
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
             "please consider having a single goal at a time"
  end;
  add_hyp id [Expr.Formula.neg g];
  goals := (id, g) :: !goals

let get_goals () = !goals

let clear_goals () = goals := []

(* Proof contextx *)
(* ************************************************************************ *)

module Ctx = struct

  module Hf = Hashtbl.Make(Expr.Formula)

  exception No_prefix

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
  let find t = Hf.find t.names

  let new_name t =
    let () = t.count <- t.count + 1 in
    Format.sprintf "%s%d" t.prefix t.count

  let add_aux t f =
    match Hf.find t.names f with
    | (f', name) -> f', name
    | exception Not_found ->
      let name = new_name t in
      let res = (f, name) in
      Hf.add t.names f res;
      res

  (* Printing *)
  let named t fmt f =
    let (f', name) = add_aux t f in
    t.wrapper CCFormat.(const string name) fmt (f, f')

  (* Wrappers *)
  let add t f = ignore (add_aux t f)
  let name t f = Format.asprintf "%a" (named t) f

end

