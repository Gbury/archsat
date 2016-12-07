
let section = Util.Section.make ~parent:Dispatcher.section "functions"

module H = Backtrack.HashtblBack(Expr.Term)

let st = H.create Dispatcher.stack

let mk_proof l = Dispatcher.mk_proof ~term_args:l "uf" "f-eq"

let set_interpretation t = fun () ->
  Util.debug ~section 10 "Check interpretation of %a" Expr.Debug.term t;
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
              let eqs = List.map2 (fun a b -> Expr.Formula.neg (Expr.Formula.eq a b)) l r in
              if Expr.(Term.equal u_v Builtin.Misc.p_true) then begin
                let res = Expr.Formula.pred t :: Expr.Formula.neg (Expr.Formula.pred t') :: eqs in
                let proof = mk_proof (t :: t' :: []) in
                raise (Dispatcher.Absurd (res, proof))
              end else begin
                let res = Expr.Formula.pred t' :: Expr.Formula.neg (Expr.Formula.pred t) :: eqs in
                let proof = mk_proof (t' :: t :: []) in
                raise (Dispatcher.Absurd (res, proof))
              end
            | { Expr.term = Expr.App (_, _, r) } ->
              let eqs = List.map2 (fun a b -> Expr.Formula.neg (Expr.Formula.eq a b)) l r in
              let res = Expr.Formula.eq t t' :: eqs in
              let proof = mk_proof (t :: t' :: []) in
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

;;
Dispatcher.Plugin.register "uf"
  ~descr:"Ensures consistency of assignments for function applications."
  (Dispatcher.mk_ext ~section ~peek:uf_pre ())
