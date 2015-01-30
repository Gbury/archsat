
let log_section = Util.Section.make "meta"
let log i fmt = Util.debug ~section:log_section i fmt

module H = Hashtbl.Make(Expr.Formula)
module S = Backtrack.HashtblBack(Expr.Term)

let id = Dispatcher.new_id ()
let no_inst = ref false

(* Set-hashtbl to tag translated formulas *)
let seen = H.create 256

let has_been_seen f =
    try ignore (H.find seen f); true
    with Not_found -> false

let mark f lvl = H.add seen f lvl

(* Small helper *)
let mk_proof f metas = id, "meta", [f], metas

(* Set of predicates to unify *)
let true_preds = S.create Dispatcher.stack
let false_preds = S.create Dispatcher.stack

let mem x tbl = try ignore (S.find tbl x); true with Not_found -> false

let inst p notp =
  let l = Unif.S.bindings (Unif.cached_unify p notp) in
  log 1 "Found inst :";
  List.iter (fun (m, t) -> log 1 " |- %a -> %a" Expr.debug_meta m Expr.debug_term t) l;
  if not !no_inst then begin
    let insts = Inst.instanciations id l in
    List.iter (fun (cl, proof) -> Dispatcher.push cl proof) insts
  end

let find_inst p notp _ =
    try
        inst p notp;
        inst notp p
    with Unif.Not_unifiable -> ()

(* Assuming function *)
let meta_assume lvl = function
    (* Term metas generation *)
    | { Expr.formula = Expr.All (l, p) } as f ->
      if not (has_been_seen f) then begin
        mark f lvl; (* Do not re-generate metas *)
        let metas = List.map Expr.term_of_meta (Expr.term_metas f lvl) in
        let subst = List.fold_left2 (fun s v t -> Expr.Subst.bind v t s) Expr.Subst.empty l metas in
        let q = Expr.formula_subst Expr.Subst.empty subst p in
        Dispatcher.push [Expr.f_not f; q] (mk_proof f metas)
      end
    | { Expr.formula = Expr.Not { Expr.formula = Expr.Ex (l, p) } } as f ->
      if not (has_been_seen f) then begin
        mark f lvl; (* Do not re-generate metas *)
        let metas = List.map Expr.term_of_meta (Expr.term_metas f lvl) in
        let subst = List.fold_left2 (fun s v t -> Expr.Subst.bind v t s) Expr.Subst.empty l metas in
        let q = Expr.formula_subst Expr.Subst.empty subst p in
        Dispatcher.push [Expr.f_not f; Expr.f_not q] (mk_proof f metas)
      end
    (* Unification discovery *)
    | { Expr.formula = Expr.Pred p } ->
      if not (mem p true_preds) then begin
        S.iter (find_inst p) false_preds;
        S.add true_preds p 0
      end
    | { Expr.formula = Expr.Not { Expr.formula = Expr.Pred p } } ->
      if not (mem p false_preds) then begin
        S.iter (find_inst p) true_preds;
        S.add false_preds p 0
      end
    | _ -> ()

let meta_eval _ = None

let meta_pre _ = ()
;;
Dispatcher.register_options [
    "-no-inst", Arg.Set no_inst,
    " Do no instanciations other than metavariables (for universally quantified formulas)"
]
;;
Dispatcher.(register {
    id = id;
    name = "meta";
    assume = (fun (f, lvl) -> meta_assume lvl f);
    eval_pred = meta_eval;
    preprocess = meta_pre;
  })

