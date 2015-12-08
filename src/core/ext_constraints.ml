
let section = Util.Section.make ~parent:Dispatcher.section "constraints"

(* Options *)
(* ************************************************************************ *)

let need_restart = ref false

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

(* Builtin symbol *)
(* ************************************************************************ *)

type Expr.builtin += Acc of t

let make_builtin acc =
  let builtin = Acc acc in
  let p = Expr.Id.term_fun ~builtin (Format.sprintf "acc#%d" acc.id) [] [] Expr.Ty.prop in
  Expr.Formula.pred (Expr.Term.apply p [] [])


(* Accumulators *)
(* ************************************************************************ *)

let unif_empty =
  let gen = function
    | [] ->
      Gen.singleton Unif.empty
    | l ->
      let open Ext_meta in
      let st = parse_slice (fun f -> List.iter f l) in
      let gen = Gen.(
          append
            (of_list st.inequalities)
            (product (of_list st.true_preds) (of_list st.false_preds))
        ) in
      Gen.filter_map (fun (t, t') ->
          match Unif.Robinson.find ~section t t' with
          | None ->
            Util.debug ~section 50 "Failed to unify:";
            Util.debug ~section 50 " - %a" Expr.Debug.term t;
            Util.debug ~section 50 " - %a" Expr.Debug.term t';
            None
          | Some s ->
            Util.debug ~section 50 "Produced : %a" Unif.debug s;
            Some s
        ) gen
  in
  let map (s, s') = match Unif.combine s s' with
    | None ->
      Util.debug ~section 50 "Failed to merge:";
      Util.debug ~section 50 " - %a" Unif.debug s;
      Util.debug ~section 50 " - %a" Unif.debug s';
      (fun () -> None)
    | Some s'' ->
      Util.debug ~section 50 "New merged: %a" Unif.debug s'';
      Gen.singleton s''
  in
  Constraints.from_merger gen map

let gen_of_acc : type a. a acc -> Constraints.t = function
  | Empty -> unif_empty
  | Acc (_, _, g) -> g

(* Parsing entry formulas *)
(* ************************************************************************ *)

let parse iter =
  let acc = ref None in
  let exprs = ref [] in
  let aux = function
    | { Expr.formula = Expr.Pred { Expr.term = Expr.App ({ Expr.builtin = Acc t }, _, _) } } ->
      begin match !acc with
        | None -> acc := Some t
        | Some t' ->
          let new_acc =
            if t.id > t'.id then (assert (belong t'.acc t.acc); t)
            else                 (assert (belong t.acc t'.acc); t')
          in
          acc := Some new_acc
      end
    | e -> exprs := e :: !exprs
  in
  let () = iter aux in
  !acc, !exprs

let handle_aux iter acc l =
  let c = gen_of_acc acc in
  match Constraints.add_constraint c l with
  | Some c' ->
    Util.debug ~section 5 "New constraint";
    Solver.assume [
      List.map Expr.Formula.neg l;
      [make_builtin (make (Acc (acc, l, c')))];
    ]
  | None ->
    Util.debug ~section 2 "Couldn't find a satisfiable constraint";
    iter Ext_meta.do_formula;
    need_restart := true;
    raise Solver.Restart

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dispatcher.If_sat iter ->
    begin match parse iter with
      | None, l ->
        Util.debug ~section 5 "Generating empty constraint";
        handle_aux iter Empty l
      | Some t, l ->
        Util.debug ~section 10 "Found previous constraint";
        handle_aux iter t.acc l
    end;
    Some ()
  | Solver.Found _ ->
    if !need_restart then
      Some Solver.Ok
    else
      None
  | _ -> None

;;
Dispatcher.Plugin.register "constraints"
  ~descr:"Handles instanciation using constraints to close multiple branches at the same time"
  (Dispatcher.mk_ext ~section ~handle:{Dispatcher.handle=handle} ())
