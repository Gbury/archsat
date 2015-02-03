
let log_section = Util.Section.make "meta"
let log i fmt = Util.debug ~section:log_section i fmt

module H = Hashtbl.Make(Expr.Formula)
module S = Backtrack.HashtblBack(Expr.Term)
module U = Hashtbl.Make(Unif.S)

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
let unif_set = U.create 256
let true_preds = S.create Dispatcher.stack
let false_preds = S.create Dispatcher.stack

let mem x tbl = S.mem tbl x

let print_aux fl tl =
    let rec aux = function
        | [] -> ()
        | x :: v :: r ->
          log 3 " | %a -> %a" Expr.debug_term x Expr.debug_term v;
          aux r
        | [_] -> assert false
    in
    begin match fl with
    | [f;p] ->
            log 1 "Inst : %a" Expr.debug_formula f;
            aux tl;
            log 1 "Res : %a" Expr.debug_formula p
    | _ -> assert false
    end

let inst p notp =
  let unif = Unif.cached_unify p notp in
  if not (U.mem unif_set unif) then begin
    U.add unif_set unif 0;
    let l = Unif.S.bindings unif in
    log 10 "Found inst";
    List.iter (fun (m, t) -> log 5 " |- %a -> %a" Expr.debug_meta m Expr.debug_term t) l;
    if not !no_inst then begin
      let (cl, ((_, _, fl, tl) as proof)) = Inst.instanciation id l in
      print_aux fl tl;
      Dispatcher.push cl proof
    end
  end

let find_inst p notp =
    try
        log 5 "Matching : %a ~~ %a" Expr.debug_term p Expr.debug_term notp;
        inst p notp;
        inst notp p
    with Unif.Not_unifiable (a, b) ->
        log 15 "Couldn't unify %a and %a" Expr.debug_term a Expr.debug_term b

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
        S.add true_preds p lvl
      end
    | { Expr.formula = Expr.Not { Expr.formula = Expr.Pred p } } ->
      if not (mem p false_preds) then begin
        S.add false_preds p lvl
      end
    | _ -> ()

let find_all_insts () =
  S.iter (fun p _ -> S.iter (fun notp _ -> find_inst p notp) false_preds) true_preds

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
    if_sat = find_all_insts;
  })

