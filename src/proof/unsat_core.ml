(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

module D = Dispatcher
module P = Solver.Proof

(* Proof nodes set *)
(* ************************************************************************ *)

let lit a = a.Dispatcher.SolverTypes.lit

let compare_clause =
  CCOrd.(map P.to_list (list (map lit Expr.Formula.compare)))

module S = Set.Make(struct
    type t = P.proof_node

    let discr = function
      | P.Hypothesis -> 0
      | P.Assumption -> 1
      | P.Lemma _ -> 2
      | P.Duplicate _ -> 3
      | P.Resolution _ -> 4

    let compare n1 n2 =
      match n1.P.step, n2.P.step with
      | P.Lemma l1, P.Lemma l2 ->
        let open CCOrd in
        map (fun l -> l.D.plugin_name) compare l1 l2
        <?> (map (fun l -> l.D.proof_name) compare, l1, l2)
        <?> (compare_clause, n1.P.conclusion, n2.P.conclusion)
      | P.Hypothesis, P.Hypothesis
      | P.Assumption, P.Assumption
      | P.Duplicate _, P.Duplicate _
      | P.Resolution _, P.Resolution _ ->
        compare_clause n1.P.conclusion n2.P.conclusion
      | a, b -> Pervasives.compare (discr a) (discr b)

  end)


(* Printing proof nodes *)
(* ************************************************************************ *)

let pp_step fmt = function
  | P.Hypothesis -> Format.fprintf fmt "hyp"
  | P.Assumption -> Format.fprintf fmt "assumption"
  | P.Lemma l -> Format.fprintf fmt "%s/%s" l.D.plugin_name l.D.proof_name
  | _ -> assert false

let pp_conclusion fmt c =
  let l = List.map lit (P.to_list c) in
  CCFormat.(list ~sep:(return "@ ||@ ")) Expr.Print.formula fmt l

let pp_node fmt node =
  Format.fprintf fmt "%a: @[<hov>%a@]@."
    pp_step node.P.step pp_conclusion node.P.conclusion


(* Sorting proof nodes *)
(* ************************************************************************ *)

let mk proof =
  let aux s node =
    match node.P.step with
    | P.Hypothesis
    | P.Assumption
    | P.Lemma _ -> S.add node s
    | P.Duplicate _
    | P.Resolution _ -> s
  in
  P.fold aux S.empty proof

let print fmt proof =
  let s = mk proof in
  S.iter (pp_node fmt) s

