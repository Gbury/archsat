
let section = Section.make "proving"

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

