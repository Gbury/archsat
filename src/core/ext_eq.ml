
let section = Section.make ~parent:Dispatcher.section "eq"

(* Module initialisation *)
(* ************************************************************************ *)

module D = Dispatcher
module E = Closure.Eq(Expr.Term)

module S = Set.Make(Expr.Term)
module M = Map.Make(Expr.Id.Const)

type info =
  | Trivial of Expr.formula
  | Chain of Expr.term list

type D.lemma_info += Eq of info

(* Union-find payloads and callbacks *)
(* ************************************************************************ *)

type load = {
  vars : Expr.term list;
  elts : Expr.term list M.t;
}

let print fmt t =
  Format.fprintf fmt "< %a >" Expr.Term.print (E.repr t)

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
    ~section:(Section.make ~parent:section "union-find")
    ~gen ~merge ~callback D.stack

(* Accessors to the equality closure *)
(* ************************************************************************ *)

module Class = struct

  type t = load E.eq_class

  let find x = E.get_class st x

  let repr t = E.repr t

  let ty t = Expr.((E.repr t).t_type)

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
  match l with
  | [] -> assert false
  | [x] ->
    let f = Expr.Formula.(eq x x) in
    Dispatcher.mk_proof name "trivial" (Eq (Trivial f))
  | _ ->
    Dispatcher.mk_proof name "eq-trans" (Eq (Chain l))

let wrap f x y =
  try
    f st x y
  with E.Unsat (a, b, l) ->
    Util.info ~section "Error while adding hypothesis : %a ~ %a@ @[<hov>{%a}@]"
      Expr.Print.term x Expr.Print.term y
      CCFormat.(list ~sep:(return ",@ ") Expr.Print.term) l;
    raise (D.Absurd (mk_expl (a, b, l), mk_proof l))

let tag x = fun () ->
  try
    Util.debug ~section "Tagging %a -> %a"
      Expr.Print.term x Expr.Print.term (D.get_assign x);
    E.add_tag st x (D.get_assign x)
  with E.Unsat (a, b, l) ->
    Util.info ~section "Error while tagging : %a -> %a@ @[<hov>{%a}@]"
      Expr.Print.term x Expr.Print.term (D.get_assign x)
      CCFormat.(list ~sep:(return ",@ ") Expr.Print.term) l;
    let res = mk_expl (a, b, l) in
    let proof = mk_proof l in
    raise (D.Absurd (res, proof))

let eq_assign x =
  try
    Util.debug ~section "Looking up tag for: %a" Expr.Print.term x;
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
    Expr.Id.set_valuation v 0 (Expr.Assign eq_assign)

let rec set_handler_term = function
  | { Expr.term = Expr.Var v } -> assert false
  | { Expr.term = Expr.Meta m } -> set_handler_aux Expr.(m.meta_id)
  | { Expr.term = Expr.App (f, _, l) } ->
    if not Expr.(Ty.equal f.id_type.fun_ret Ty.prop) then begin
      Util.debug ~section "setting handler for %a" Expr.Id.print f;
      Expr.Id.set_valuation f 0 (Expr.Assign eq_assign)
    end;
    List.iter set_handler_term l

let rec set_handler = function
  | { Expr.formula = Expr.Equal (a, b) } when Expr.Term.equal a b ->
    set_handler_term a
  | { Expr.formula = Expr.Equal (a, b) } ->
    set_handler_term a;
    set_handler_term b
  | { Expr.formula = Expr.Pred p } ->
    set_handler_term p
  | { Expr.formula = Expr.Not f } ->
    set_handler f
  | _ -> ()

let rec set_watcher_term t =
  if not Expr.(Ty.equal t.t_type Ty.prop) then
    watch 1 [t] (tag t);
  match t with
  | { Expr.term = Expr.Var v } -> assert false
  | { Expr.term = Expr.Meta m } -> ()
  | { Expr.term = Expr.App (f, _, l) } -> List.iter set_watcher_term l

let rec set_watcher = function
  | { Expr.formula = Expr.Equal (a, b) } as f when Expr.Term.equal a b ->
    D.push [f] (D.mk_proof name "trivial" (Eq (Trivial f)));
    set_watcher_term a
  | { Expr.formula = Expr.Equal (a, b) } as f ->
    watch 1 [a; b] (f_eval f);
    set_watcher_term a;
    set_watcher_term b
  | { Expr.formula = Expr.Pred p } ->
    set_watcher_term p
  | { Expr.formula = Expr.Not f } ->
    set_watcher f
  | _ -> ()

(* Proof managament *)
(* ************************************************************************ *)

let dot_info = function
  | Trivial _ -> None, []
  | Chain l -> None, List.map (CCFormat.const Dot.Print.term) l

let to_eqs l =
  let rec aux first acc = function
    | [] -> assert false
    | [last] ->
      Expr.Formula.eq first last, List.rev acc
    | x :: ((y :: _) as r) ->
      aux first (Expr.Formula.eq x y :: acc) r
  in
  match l with
  | [] | [_] -> assert false
  | first :: _ -> aux first [] l

(*
let rec coq_aux m fmt = function
  | [] -> assert false
  | [x] ->
    Format.fprintf fmt "%a" (Proof.Ctx.named m) x
  | x :: r ->
    Format.fprintf fmt "(eq_trans %a %a)"
      (Proof.Ctx.named m) x (coq_aux m) r

let coq_proof = function
  | Trivial f ->
    Coq.tactic (fun fmt ctx ->
        Coq.exact fmt "%a eq_refl" (Proof.Ctx.named ctx) (Expr.Formula.neg f)
      )
  | Chain l ->
    let res, eqs = to_eqs (List.rev l) in
    Coq.tactic ~prefix:"E" (fun fmt ctx ->
        Format.fprintf fmt "exact (%a %a)."
          (Proof.Ctx.named ctx) (Expr.Formula.neg res)
          (coq_aux ctx) eqs
      )
*)

(* Handler & Plugin registering *)
(* ************************************************************************ *)

let handle : type ret. ret D.msg -> ret option = function
  | Dot.Info Eq info -> Some (dot_info info)
  (* | Coq.Tactic Eq info -> Some (coq_proof info) *)
  | _ -> None

let register () =
  D.Plugin.register name
    ~descr:"Ensures consistency of assignment with regards to the equality predicates."
    (D.mk_ext ~handle:{D.handle} ~section ~assume ~set_handler ~set_watcher ~eval_pred ())

