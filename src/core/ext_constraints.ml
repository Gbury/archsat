
let section = Util.Section.make ~parent:Dispatcher.section "constraints"

(* Accumulators for constraints *)
(* ************************************************************************ *)

type zero
type succ

type _ acc =
  | Empty : zero acc
  | Acc : _ acc * Expr.formula list * Constraints.t -> succ acc
(* A type for constraints accumulators. the type parameter indicates wether
   the constraint is empty or not.
   Acc(acc, l, c) is so that c is the enumeration of constraints
   that satisfy acc, and induce a contradiction in some formuylas of l *)

type t = {
  id : int;
  acc : succ acc;
}
(* Accumulators are tagged with an increasing id in order to know which accumulator
   is more recent when comparing two *)

let rec belong : type l. succ acc -> l acc -> bool =
  fun a b -> match b with
    | Empty -> false
    | Acc (a', _, _) -> a == b || belong a a'
(* We test wether a non-empty acc is a sub-accumulator of another accumulator
   (which can possibly be empty). *)

let make =
  let c = ref 0 in
  (fun acc -> incr c; { id = !c; acc })


;;
Dispatcher.Plugin.register "constraints"
  ~descr:"Handles instanciation using constraints to close multiple branches at the same time"
  (Dispatcher.mk_ext ~section ())
