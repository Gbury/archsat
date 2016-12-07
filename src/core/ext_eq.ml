
let section = Util.Section.make ~parent:Dispatcher.section "eq"

module D = Dispatcher
module E = Eclosure.Make(Expr.Term)

let st = E.create D.stack (Util.Section.make ~parent:section "union-find")

let name = "eq"
let watch = D.watch name

let eq_eval = function
  | { Expr.formula = Expr.Equal (a, b) } as f ->
    begin try
        let a' = D.get_assign a in
        let b' = D.get_assign b in
        Util.debug ~section 30 "Eval [%a] %a == %a" Expr.Debug.formula f Expr.Debug.term a' Expr.Debug.term b';
        Some (Expr.Term.equal a' b', [a; b])
      with D.Not_assigned _ ->
        None
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b) } } as f ->
    begin try
        let a' = D.get_assign a in
        let b' = D.get_assign b in
        Util.debug ~section 30 "Eval [%a] %a <> %a" Expr.Debug.formula f Expr.Debug.term a' Expr.Debug.term b';
        Some (not (Expr.Term.equal a' b'), [a; b])
      with D.Not_assigned _ ->
        None
    end
  | _ -> None

let f_eval f () =
  match eq_eval f with
  | Some(true, lvl) -> D.propagate f lvl
  | Some(false, lvl) -> D.propagate (Expr.Formula.neg f) lvl
  | None -> ()

let mk_expl (a, b, l) =
  let rec aux acc = function
    | [] | [_] -> acc
    | x :: ((y :: _) as r) ->
      aux (Expr.Formula.eq x y :: acc) r
  in
  (Expr.Formula.eq a b) :: (List.rev_map Expr.Formula.neg (aux [] l))

let mk_proof l =
  assert (l <> []);
  Dispatcher.mk_proof name ~term_args:l "eq-trans"

let wrap f x y =
  try
    f st x y
  with E.Unsat (a, b, l) ->
    Util.debug ~section 2 "Error while adding hypothesis : %a ~ %a" Expr.Debug.term x Expr.Debug.term y;
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let tag x = fun () ->
  try
    Util.debug ~section 10 "Tagging %a" Expr.Debug.term x;
    E.add_tag st x (D.get_assign x)
  with E.Unsat (a, b, l) ->
    Util.debug ~section 2 "Error while tagging : %a -> %a" Expr.Debug.term x Expr.Debug.term (D.get_assign x);
    let res = mk_expl (a, b, l) in
    let proof = mk_proof l in
    raise (D.Absurd (res, proof))

let eq_assign x =
  try
    begin match E.find_tag st x with
      | _, Some (_, v) ->
        Util.debug ~section 5 "Found tag : %a" Expr.Debug.term v;
        v
      | x, None ->
        Util.debug ~section 5 "Looking up repr : %a" Expr.Debug.term x;
        let res = try D.get_assign x with D.Not_assigned _ -> x in
        res
    end
  with E.Unsat (a, b, l) ->
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let eq_assume = function
  | { Expr.formula = Expr.Equal (a, b)} ->
    wrap E.add_eq a b;
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b)} } ->
    wrap E.add_neq a b;
  | _ -> ()

let rec set_handler t =
  let aux v =
    if not Expr.(Ty.equal v.id_type Ty.prop) then
      Expr.Id.set_assign v 0 eq_assign
  in
  if not Expr.(Ty.equal t.t_type Ty.prop) then
    watch 1 [t] (tag t);
  match t with
  | { Expr.term = Expr.Var v } -> aux v
  | { Expr.term = Expr.Meta m } -> aux Expr.(m.meta_id)
  | { Expr.term = Expr.App (f, _, l) } ->
    if not Expr.(Ty.equal f.id_type.fun_ret Ty.prop) then
      Expr.Id.set_assign f 0 eq_assign;
    List.iter set_handler l

let rec eq_pre = function
  | { Expr.formula = Expr.Equal (a, b) } as f when Expr.Term.equal a b ->
    D.push [f] (D.mk_proof "ext_eq" "trivial");
    set_handler a
  | { Expr.formula = Expr.Equal (a, b) } as f ->
    watch 1 [a; b] (f_eval f);
    set_handler a;
    set_handler b
  | { Expr.formula = Expr.Pred p } ->
    set_handler p
  | { Expr.formula = Expr.Not f } ->
    eq_pre f
  | _ -> ()

;;
D.Plugin.register name
  ~descr:"Ensures consistency of assignment with regards to the equality predicates."
  (D.mk_ext ~section
     ~assume:eq_assume
     ~eval_pred:eq_eval
     ~peek:eq_pre
     ()
  )
