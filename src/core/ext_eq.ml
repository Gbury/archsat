
let section = Util.Section.make ~parent:Dispatcher.section "eq"

(* Module initialisation *)
(* ************************************************************************ *)

module D = Dispatcher
module E = Closure.Eq(Expr.Term)

module S = Set.Make(Expr.Term)
module M = Map.Make(Expr.Id.Const)

(* Union-find payloads and callbacks *)
(* ************************************************************************ *)

type load = {
  vars : Expr.term list;
  elts : Expr.term list M.t;
}

let print fmt t =
  Format.fprintf fmt "<< %a >>" Expr.Term.print (E.repr t)

let gen = function
  | { Expr.term = Expr.Var _ } ->
    assert false
  | { Expr.term = Expr.Meta _ } as t ->
    { vars = [t]; elts = M.empty; }
  | { Expr.term = Expr.App (f, _, _) } as t ->
    { vars = []; elts = M.singleton f [t]; }

let merge a b =
  let vars = a.vars @ b.vars in
  let aux _ x y = match x, y with
    | None, None -> None
    | Some l, Some l' -> Some (l @ l')
    | Some l, None | None, Some l -> Some l
  in
  { vars; elts = M.merge aux a.elts b.elts; }

let callback, register_callback =
  let l = ref [] in
  let callback a b c =
    Util.debug ~section "Merging %a / %a ==> %a"
      print a print b print c;
    List.iter (fun (name, f) ->
        if Dispatcher.Plugin.(is_active (find name)) then
          f a b c) !l
  in
  let register name f =
    l := (name, f) :: !l
  in
  callback, register

let st = E.create
    ~section:(Util.Section.make ~parent:section "union-find")
    ~gen ~merge ~callback D.stack

(* Accessors to the equality closure *)
(* ************************************************************************ *)

module Class = struct

  type t = load E.eq_class

  let find x = E.get_class st x

  let repr t = E.repr t

  let hash c = Expr.Term.hash (repr c)
  let equal c c' = Expr.Term.equal (repr c) (repr c')
  let compare c c' = Expr.Term.compare (repr c) (repr c')

  let print = print

  let mem t x =
    Expr.Term.equal (repr t) (repr (find x))

  let fold f x t =
    let l = E.load t in
    let aux _ l acc = List.fold_left f acc l in
    M.fold aux l.elts (List.fold_left f x l.vars)

  let find_top t f =
    let load = E.load t in
    try M.find f load.elts
    with Not_found -> []

end

(* McSat Plugin for equality *)
(* ************************************************************************ *)

let name = "eq"
let watch = D.watch name

let eval_pred = function
  | { Expr.formula = Expr.Equal (a, b) } as f ->
    begin try
        let a' = D.get_assign a in
        let b' = D.get_assign b in
        Util.debug ~section "Eval [%a] %a == %a"
            Expr.Print.formula f Expr.Print.term a' Expr.Print.term b';
        Some (Expr.Term.equal a' b', [a; b])
      with D.Not_assigned _ ->
        None
    end
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b) } } as f ->
    begin try
        let a' = D.get_assign a in
        let b' = D.get_assign b in
        Util.debug ~section "Eval [%a] %a <> %a"
            Expr.Print.formula f Expr.Print.term a' Expr.Print.term b';
        Some (not (Expr.Term.equal a' b'), [a; b])
      with D.Not_assigned _ ->
        None
    end
  | _ -> None

let f_eval f () =
  match eval_pred f with
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
    Util.info ~section "Error while adding hypothesis : %a ~ %a"
      Expr.Print.term x Expr.Print.term y;
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let tag x = fun () ->
  try
    Util.debug ~section "Tagging %a -> %a"
      Expr.Print.term x Expr.Print.term (D.get_assign x);
    E.add_tag st x (D.get_assign x)
  with E.Unsat (a, b, l) ->
    Util.info ~section "Error while tagging : %a -> %a"
      Expr.Print.term x Expr.Print.term (D.get_assign x);
    let res = mk_expl (a, b, l) in
    let proof = mk_proof l in
    raise (D.Absurd (res, proof))

let eq_assign x =
  try
    begin match E.find_tag st x with
      | _, Some (_, v) ->
        Util.debug ~section "Found tag : %a" Expr.Print.term v;
        v
      | x, None ->
        Util.debug ~section "Looking up repr : %a" Expr.Print.term x;
        let res = try D.get_assign x with D.Not_assigned _ -> x in
        res
    end
  with E.Unsat (a, b, l) ->
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let assume = function
  | { Expr.formula = Expr.Equal (a, b)} ->
    wrap E.add_eq a b;
  | { Expr.formula = Expr.Not { Expr.formula = Expr.Equal (a, b)} } ->
    wrap E.add_neq a b;
  | _ -> ()

let set_handler_aux v =
  if not Expr.(Ty.equal v.id_type Ty.prop) then
    Expr.Id.set_assign v 0 eq_assign

let rec set_handler t =
  if not Expr.(Ty.equal t.t_type Ty.prop) then
    watch 1 [t] (tag t);
  match t with
  | { Expr.term = Expr.Var v } -> set_handler_aux v
  | { Expr.term = Expr.Meta m } -> set_handler_aux Expr.(m.meta_id)
  | { Expr.term = Expr.App (f, _, l) } ->
    if not Expr.(Ty.equal f.id_type.fun_ret Ty.prop) then
      Expr.Id.set_assign f 0 eq_assign;
    List.iter set_handler l

let rec peek = function
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
    peek f
  | _ -> ()

let register () =
  D.Plugin.register name
    ~descr:"Ensures consistency of assignment with regards to the equality predicates."
    (D.mk_ext ~section ~assume ~peek ~eval_pred ())

