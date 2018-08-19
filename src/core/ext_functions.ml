(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

let section = Section.make ~parent:Dispatcher.section "functions"

let name = "uf"

(* Module aliases & wrappers *)
(* ************************************************************************ *)

module H = Backtrack.Hashtbl(Expr.Term)

type info =
  | Fun of Expr.term list * Expr.term list *
           Expr.Id.Const.t * Expr.term * Expr.term
  | Pred of Expr.term list * Expr.term list *
            Expr.Id.Const.t * Expr.formula * Expr.formula

type Dispatcher.lemma_info += UF of info

let mk_proof info =
  Dispatcher.mk_proof "uf" "f-eq" (UF info)

(* Module initialisation *)
(* ************************************************************************ *)

let st = H.create Dispatcher.stack

let set_interpretation t = fun () ->
  Util.debug ~section "Check interpretation of %a" Expr.Print.term t;
    match t with
    | { Expr.term = Expr.App (f, tys, l) } ->
      let is_prop = Expr.(Ty.equal t.t_type Ty.prop) in
      let t_v = Dispatcher.get_assign t in
      let l' = List.map (fun x -> Dispatcher.get_assign x) l in
      let u = Expr.Term.apply f tys l' in
      begin try
          let t', u_v = H.find st u in
          if not (Expr.Term.equal t_v u_v) then begin
            match t' with
            | { Expr.term = Expr.App (_, _, r) } when is_prop ->
              let p = Expr.Formula.pred t in
              let p' = Expr.Formula.pred t' in
              let eqs = List.map2 (fun a b -> Expr.Formula.eq a b) r l in
              let l' = List.map Expr.Formula.neg eqs in
              if Expr.(Term.equal u_v Builtin.Misc.p_true) then begin
                let res = p :: Expr.Formula.neg p' :: l' in
                let proof = mk_proof (Pred (l, r, f, p, p')) in
                raise (Dispatcher.Absurd (res, proof))
              end else begin
                let res = p' :: Expr.Formula.neg p :: l' in
                let proof = mk_proof (Pred (r, l, f, p', p)) in
                raise (Dispatcher.Absurd (res, proof))
              end
            | { Expr.term = Expr.App (_, _, r) } ->
              let eqs = List.map2 (fun a b -> Expr.Formula.eq a b) l r in
              let l' = List.map Expr.Formula.neg eqs in
              let res = Expr.Formula.eq t t' :: l' in
              let proof = mk_proof (Fun (l, r, f, t, t')) in
              raise (Dispatcher.Absurd (res, proof))
            | _ -> assert false
          end
        with Not_found ->
          H.add st u (t, t_v);
      end
    | _ -> assert false

let watch = Dispatcher.mk_watch (module Expr.Term) name

let rec set_watcher_term = function
  | { Expr.term = Expr.Var _ }
  | { Expr.term = Expr.Meta _ } -> ()
  | { Expr.term = Expr.App (f, _, l) } as t ->
    if l <> [] then watch t 1 (t :: l) (set_interpretation t);
    List.iter set_watcher_term l

let rec set_watcher = function
    | { Expr.formula = Expr.Equal (a, b) } ->
      set_watcher_term a;
      set_watcher_term b
    | { Expr.formula = Expr.Pred p } ->
      set_watcher_term p
    | { Expr.formula = Expr.Not f } ->
      set_watcher f
    | _ -> ()

(* Proof management *)
(* ************************************************************************ *)

let dot_info = function
  | Fun (_, _, _, t, t') ->
    None, List.map (CCFormat.const Dot.Print.term) [t; t']
  | Pred (_, _, _, t, t') ->
    None, List.map (CCFormat.const Dot.Print.formula) [t; t']


let coq_proof = function
  | Fun (l, r, f, a, b) -> (* We want to prove:
                               ~ ~ x1 = y1 -> ... -> ~ ~ xn = yn -> ~ f(x1,.., xn) = f(y1,..,yn) -> False
                               with l = [x1; ..; xn], r = [y1; ..; yn] *)
    let t = Term.(of_id ~kind:`Cst @@ of_function_descr of_ttype of_ty) f in
    let eqs = List.combine (List.map Term.of_term l) (List.map Term.of_term r) in
    let a_t = Term.of_term a in
    let b_t = Term.of_term b in
    let goal = Term.apply Term.equal_term [Term.ty a_t; a_t; b_t] in
    let intros = ref [] in
    (fun pos -> pos
                |> Logic.introN "E" (List.length eqs + 1)
                  ~post:(fun f pos -> intros := f :: !intros; pos)
                |> Logic.fold (Logic.normalize "E") !intros
                |> Logic.find (Term.app Term.not_term goal) @@ Logic.apply1 []
                |> Eq.congruence_term t eqs)
  | Pred (l, r, f, a, b) -> (* We want to prove:
                               ~ ~ x1 = y1 -> ... -> ~ ~ xn = yn -> ~ ~ f(x1,.., xn) -> ~ f(y1,..,yn) -> False
                               with l = [x1; ..; xn], r = [y1; ..; yn], a = f(x1, ..,xn), b = f(y1,..,yn) *)
    let t = Term.(of_id ~kind:`Cst @@ of_function_descr of_ttype of_ty) f in
    let eqs = List.combine (List.map Term.of_term l) (List.map Term.of_term r) in
    let a_t = Term.of_formula a in
    let intros = ref [] in
    (fun pos -> pos
                |> Logic.introN "E" (List.length eqs + 2)
                  ~post:(fun f pos -> intros := f :: !intros; pos)
                |> Logic.fold (Logic.normalize "E") !intros
                |> Logic.find (Term.app Term.not_term a_t) @@ Logic.apply1 []
                |> Eq.congruence_prop t eqs)


(* Plugin registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info UF info -> Some (dot_info info)
  | Proof.Lemma UF info -> Some (coq_proof info)
  | _ -> None

let register () =
  Dispatcher.Plugin.register name
    ~descr:"Ensures consistency of assignments for function applications."
    (Dispatcher.mk_ext ~handle:{Dispatcher.handle} ~section ~set_watcher ())

