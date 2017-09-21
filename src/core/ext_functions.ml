
let section = Section.make ~parent:Dispatcher.section "functions"

(* Module aliases & wrappers *)
(* ************************************************************************ *)

module H = Backtrack.Hashtbl(Expr.Term)

type info =
  | Fun of Expr.formula list * Expr.term * Expr.term
  | Pred of Expr.formula list * Expr.formula * Expr.formula

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
              let l = List.map Expr.Formula.neg eqs in
              if Expr.(Term.equal u_v Builtin.Misc.p_true) then begin
                let res = p :: Expr.Formula.neg p' :: l in
                let proof = mk_proof (Pred (eqs, p, p')) in
                raise (Dispatcher.Absurd (res, proof))
              end else begin
                let res = p' :: Expr.Formula.neg p :: l in
                let proof = mk_proof (Pred (eqs, p', p)) in
                raise (Dispatcher.Absurd (res, proof))
              end
            | { Expr.term = Expr.App (_, _, r) } ->
              let eqs = List.map2 (fun a b -> Expr.Formula.eq a b) l r in
              let l = List.map Expr.Formula.neg eqs in
              let res = Expr.Formula.eq t t' :: l in
              let proof = mk_proof (Fun (eqs, t, t')) in
              raise (Dispatcher.Absurd (res, proof))
            | _ -> assert false
          end
        with Not_found ->
          H.add st u (t, t_v);
      end
    | _ -> assert false

let rec set_handler = function
  | { Expr.term = Expr.Var _ }
  | { Expr.term = Expr.Meta _ } -> ()
  | { Expr.term = Expr.App (f, _, l) } as t ->
    if l <> [] then Dispatcher.watch "uf" 1 (t :: l) (set_interpretation t);
    List.iter set_handler l

let uf_pre = function
    | { Expr.formula = Expr.Equal (a, b) } ->
      set_handler a;
      set_handler b
    | { Expr.formula = Expr.Pred p } ->
      set_handler p
    | _ -> ()

(* Proof management *)
(* ************************************************************************ *)

let dot_info = function
  | Fun (_, t, t') ->
    None, List.map (CCFormat.const Dot.Print.term) [t; t']
  | Pred (_, t, t') ->
    None, List.map (CCFormat.const Dot.Print.formula) [t; t']

let coq_proof = function
  | Fun (l, t, t') ->
    Coq.tactic ~prefix:"E" (fun fmt ctx ->
        List.iter (fun eq ->
            Format.fprintf fmt "rewrite %a.@ " (Proof.Ctx.named ctx) eq) l;
        Coq.exact fmt "eq_refl"
      )
  | Pred (l, p, p') ->
    Coq.tactic ~prefix:"E" (fun fmt ctx ->
        List.iter (fun eq ->
            Format.fprintf fmt "rewrite %a.@ " (Proof.Ctx.named ctx) eq) l;
        Coq.exact fmt "%a" (Proof.Ctx.named ctx) p'
      )


(* Plugin registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info UF info -> Some (dot_info info)
  (* | Coq.Prove UF info -> Some (coq_proof info) *)
  | _ -> None

let register () =
  Dispatcher.Plugin.register "uf"
    ~descr:"Ensures consistency of assignments for function applications."
    (Dispatcher.mk_ext ~handle:{Dispatcher.handle} ~section ~peek:uf_pre ())

