
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

  module Hs = Hashtbl.Make(CCString)
  module Hf = Hashtbl.Make(Expr.Formula)

  exception No_prefix

  type t = {
    (** Prefixed formula name map *)
    count : int Hs.t;
    mutable prefix : string option;
    names : (Expr.formula * string) Hf.t;
  }

  let mk ?prefix () = {
    prefix;
    count = Hs.create 3;
    names = Hf.create 13;
  }

  (* Named formulas with a prefix. *)
  let prefix t s = t.prefix <- Some s

  let find t = Hf.find t.names

  let name t f = snd (find t f)

  let new_name t =
    match t.prefix with
    | None -> raise No_prefix
    | Some prefix ->
      let i = try Hs.find t.count prefix with Not_found -> 0 in
      let () = Hs.add t.count prefix (i + 1) in
      Format.sprintf "%s%d" prefix i

  let add_aux t f =
    match Hf.find t.names f with
    | (_, name) -> name
    | exception Not_found ->
      let name = new_name t in
      Hf.add t.names f (f, name);
      name

  let add t f = ignore (add_aux t f)

  (* Printer wrapper *)
  let named t fmt f =
    Format.fprintf fmt "%s" (add_aux t f)

end

