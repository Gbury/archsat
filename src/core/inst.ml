
let section = Section.make ~parent:Dispatcher.section "inst"

type lemma_info =
  | Formula of Expr.formula * Mapping.t * Expr.formula *
               Expr.ttype Expr.id list * Expr.ty Expr.id list

type Dispatcher.lemma_info += Inst of lemma_info

module Hm = Hashtbl.Make(Mapping)
module Hf = Hashtbl.Make(Expr.Formula)

(* Metavariable positions *)
(* ************************************************************************ *)

type cluster =
  | Root of Expr.formula
  | Under of Expr.formula * cluster

let rec root = function
  | Root f -> f
  | Under (_, c) -> root c

let rec depth = function
  | Root _ -> 0
  | Under (_, c) -> 1 + depth c

let rec dive n = function
  | c when n <= 0 -> c
  | Root _ (* n > 0 *) -> assert false
  | Under (_, c) -> dive (n - 1) c

let rec print fmt = function
  | Root f ->
    Format.fprintf fmt "%a" Expr.Formula.print f
  | Under (f, c) ->
    Format.fprintf fmt "@[<v>%a@ |- %a@]"
      Expr.Print.formula f print c

let rec compare c c' =
  match c, c' with
  | Root f, Root f' -> Expr.Formula.compare f f'
  | Under (f, d), Under (f', d') ->
    CCOrd.Infix.(Expr.Formula.compare f f'
                 <?> (compare, d, d'))
  | Root _, Under _ -> -1
  | Under _, Root _ -> 1

let cmp c c' =
  let d = depth c in
  let d' = depth c' in
  let a, b, inversed =
    if d < d' then c, c', false else c', c, true
  in
  let diff = abs (d - d') in
  let c = dive diff b in
  if compare a c = 0 then
    if diff = 0
    then Comparison.Eq
    else if inversed
    then Comparison.Gt
    else Comparison.Lt
  else Comparison.Incomparable

let mk_root f = Root f
let mk_cluster f c = Under (f, c)

(** Cluster registering *)
let tbl = Hf.create 4013

let get_cluster f =
  let q = match f with
    | { Expr.formula = Expr.All _ } -> f
    | { Expr.formula = Expr.Not ( {
        Expr.formula = Expr.Ex _ } as f' ) } -> f'
    | _ ->
      Util.error ~section "@[<hv 2>Getting cluster for:@ %a@]"
        Expr.Formula.print f;
      raise (Invalid_argument "Inst.get_cluster")
  in
  try Some (Hf.find tbl q)
  with Not_found -> None

let rec set_cluster c f =
  match f.Expr.formula with
  | Expr.Pred _
  | Expr.Equal _
  | Expr.True | Expr.False -> ()
  | Expr.Not f' -> set_cluster c f'
  | Expr.And l
  | Expr.Or l -> List.iter (set_cluster c) l
  | Expr.Imply (p, q)
  | Expr.Equiv (p, q) -> List.iter (set_cluster c) [p; q]
  | Expr.Ex (_, _, f')
  | Expr.All (_, _, f') ->
    let c' = mk_cluster f c in
    Util.debug ~section "@[<hv 2>%a@ <<--@ %a@]"
      Expr.Print.formula f print c';
    Hf.add tbl f c'; set_cluster c f'

let mark_meta quant f =
  Util.debug ~section "@[<hv 2>Marking:@ %a@ with@ %a@]"
    Expr.Print.formula quant Expr.Print.formula f;
  match quant with
  | ({ Expr.formula = Expr.All (_, _, _) } as q)
  | { Expr.formula = Expr.Not ( {
          Expr.formula = Expr.Ex (_, _, _) } as q) } ->
    let current =
      match get_cluster quant with
      | Some c -> c
      | None ->
        let c = mk_root quant in
        Util.debug ~section "@[<hv 2>%a@ <<<<@ %a@]"
          Expr.Print.formula q print c;
        Hf.add tbl q c;
        c
    in
    set_cluster current f
  | _ -> raise (Invalid_argument "Inst.mark_meta")

(* Virtual meta-variables *)
(* ************************************************************************ *)

let v_meta = Tag.create ()

let mk_ty_var =
  let i = ref 0 in
  (fun () -> incr i; Expr.Id.ttype (Format.asprintf "vty_%d" !i))

let mk_t_var =
  let i = ref 0 in
  (fun ty -> incr i; Expr.Id.ty (Format.asprintf "vt_%d" !i) ty)

let indexes l l' =
  let aux m = m.Expr.meta_index in
  CCList.sort_uniq ~cmp:Pervasives.compare (List.map aux l @ List.map aux l')

let meta_of_indexes l =
  CCFun.(l
         |> CCList.map Expr.Meta.of_index
         |> CCList.split
         |> CCPair.map CCList.flatten CCList.flatten)

let generalize_aux m =
  Util.debug ~section "Generalizing@ %a" Mapping.print m;
  let vdom, ((mtydom, mtdom) as mdom) = Mapping.domain m in
  let vtycodom, mtycodom = Mapping.ty_codomain m in
  let vtcodom, mtcodom = Mapping.term_codomain m in
  assert (Expr.Id.inter_fv vdom (vtycodom,vtcodom) = ([], []));
  assert (Expr.Meta.inter_fm mdom (mtycodom, mtcodom) = ([], []));
  let ty_l, t_l = meta_of_indexes @@ indexes (mtydom @ mtycodom) (mtdom @ mtcodom) in
  let mtycodom = CCList.filter (fun m -> not @@ CCList.mem ~eq:Expr.Meta.equal m mtydom) ty_l in
  let mtcodom = CCList.filter (fun m -> not @@ CCList.mem ~eq:Expr.Meta.equal m mtdom) t_l in
  Util.debug ~section "@[<hv 2>mtycodom: %a@]"
    CCFormat.(hvbox (list ~sep:(return ";@ ") Expr.Meta.print)) mtycodom;
  Util.debug ~section "@[<hv 2>mtcodom: %a@]"
    CCFormat.(hvbox (list ~sep:(return ";@ ") Expr.Meta.print)) mtcodom;
  assert (Expr.Id.inter_fv vdom (vtycodom,vtcodom) = ([], []));
  assert (Expr.Meta.inter_fm mdom (mtycodom, mtcodom) = ([], []));
  let vtys = List.map (fun _ -> mk_ty_var ()) vtycodom in
  let mtys = List.map (fun _ -> mk_ty_var ()) mtycodom in
  let ty_s = List.fold_left2 Mapping.Var.bind_ty m
      vtycodom (List.map Expr.Ty.of_id vtys) in
  let ty_s = List.fold_left2 Mapping.Meta.bind_ty ty_s
      mtycodom (List.map Expr.Ty.of_id mtys) in
  Util.debug ~section "@[<hv 2>ty_s:@ %a@]" Mapping.print ty_s;
  let vts = List.map (fun v -> mk_t_var (Mapping.apply_ty ty_s v.Expr.id_type)) vtcodom in
  let mts = List.map (fun m -> mk_t_var (Mapping.apply_ty ty_s Expr.(m.meta_type))) mtcodom in
  if vtys = [] && mtys = [] &&
     vts = [] && mts = [] then
    m
  else begin
    let ty_vars = vtys @ mtys in
    let term_vars = vts @ mts in
    let f = Expr.Formula.all (ty_vars, term_vars) Expr.Formula.f_true in
    let () = mark_meta f Expr.Formula.f_true in
    let l, l' = Expr.Formula.gen_metas f in
    (* is this necessary ?
       let () = mark_meta f Expr.Formula.f_true in *)
    let (vtm_ty, mtm_ty) =
      CCList.take_drop (List.length vtys) (List.map Expr.Ty.of_meta l) in
    let (vtm_t, mtm_t) =
      CCList.take_drop (List.length vts) (List.map Expr.Term.of_meta l') in
    Util.debug ~section "@[<hv 2>vtm_ty:@ [ %a ]@ [ %a ]@]"
      CCFormat.(hovbox (list ~sep:(return ";@ ") Expr.Id.print)) vtycodom
      CCFormat.(hovbox (list ~sep:(return ";@ ") Expr.Ty.print)) vtm_ty;
    Util.debug ~section "@[<hv 2>mtm_ty:@ [ %a ]@ [ %a ]@]"
      CCFormat.(hovbox (list ~sep:(return ";@ ") Expr.Meta.print)) mtycodom
      CCFormat.(hovbox (list ~sep:(return ";@ ") Expr.Ty.print)) mtm_ty;
    Util.debug ~section "@[<hv 2>vtm_t:@ [ %a ]@ [ %a ]@]"
      CCFormat.(hovbox (list ~sep:(return ";@ ") Expr.Id.print)) vtcodom
      CCFormat.(hovbox (list ~sep:(return ";@ ") Expr.Term.print)) vtm_t;
    Util.debug ~section "@[<hv 2>mtm_t:@ [ %a ]@ [ %a ]@]"
      CCFormat.(hovbox (list ~sep:(return ";@ ") Expr.Meta.print)) mtcodom
      CCFormat.(hovbox (list ~sep:(return ";@ ") Expr.Term.print)) mtm_t;
    let m' = List.fold_left2 Mapping.Var.bind_ty m vtycodom vtm_ty in
    let m' = List.fold_left2 Mapping.Var.bind_term m' vtcodom vtm_t in
    let m' = List.fold_left2 Mapping.Meta.bind_ty m' mtycodom mtm_ty in
    let m' = List.fold_left2 Mapping.Meta.bind_term m' mtcodom mtm_t in
    let m' = Mapping.apply ~fix:true m' m' in
    let m' = Mapping.filter m'
        ~ty_var:(fun _ _ -> false) ~term_var:(fun _ _ -> false)
        ~ty_meta:(fun _ _ -> true) ~term_meta:(fun _ _ -> true)
    in
    let () = Expr.Formula.tag f v_meta m' in
    Util.debug ~section "@[<hv 2>Generalized@ %a@ into@ %a@]"
      Mapping.print m Mapping.print m';
    m'
  end

let generalize =
  let cache = CCCache.unbounded ~eq:Mapping.equal ~hash:Mapping.hash 4013 in
  CCCache.with_cache cache generalize_aux

(* Instanciation helpers *)
(* ************************************************************************ *)

(* TODO: cache cluster access for meta-variables *)

module N = CCMap.Make(CCInt)
module M = CCMap.Make(Expr.Formula)

(* Given a mapping, split it into mapping
   for which all metas have the same root cluster *)
let split m =
  let aux def bind m e acc =
    let f = def m.Expr.meta_index in
    let r = match get_cluster f with
      | Some c -> root c
      | None ->
        Util.error ~section "@[<hv 2>Looking for cluster failed on:@ %a@]"
          Expr.Formula.print f;
        raise (Invalid_argument "Inst.split")
    in
    Util.debug ~section "split | %a : %a" Expr.Meta.print m Expr.Print.formula r;
    let s = M.get_or ~default:Mapping.empty r acc in
    M.add r (bind s m e) acc
  in
  let tmp =
    Mapping.fold m M.empty
      ~ty_var:(fun _ _ _ -> assert false)
      ~ty_meta:(aux Expr.Meta.def Mapping.Meta.bind_ty)
      ~term_var:(fun _ _ _ -> assert false)
      ~term_meta:(aux Expr.Meta.def Mapping.Meta.bind_term)
  in
  M.fold (fun _ m acc -> m :: acc) tmp []

(* Find the miniaml cluster in a mapping where all meta definitions
   are supposed to be comparable (as is the case in theoutput of split). *)
let min_cluster mapping =
  let aux def m e acc =
    let f = def m.Expr.meta_index in
    match get_cluster f, acc with
    | Some c, None -> Some c
    | Some c, Some c' ->
      begin match cmp c c' with
        | Comparison.Lt -> Some c
        | Comparison.Incomparable ->
          Util.warn ~section "@[<hv 2>Non-comparable clusters in mapping@ %a@]"
            Mapping.print mapping;
          acc
        | _ -> acc
      end
    | None, _ ->
      Util.error ~section "Defining formula for meta %a doesn't have a cluster"
        Expr.Print.meta m;
      assert false
  in
  Mapping.fold mapping None
    ~ty_var:(fun _ _ _ -> assert false)
    ~ty_meta:(aux Expr.Meta.def)
    ~term_var:(fun _ _ _ -> assert false)
    ~term_meta:(aux Expr.Meta.def)

(** Take a map, and filter out all metas but for the
    smallest cluster. *)
let reduce_map s =
  match min_cluster s with
  | None -> assert false
  | Some c ->
    let aux def m e =
      let f = def m.Expr.meta_index in
      match get_cluster f with
      | None -> assert false
      | Some c' -> compare c c' = 0
    in
    Mapping.filter s
      ~ty_var:(fun _ _ -> assert false)
      ~ty_meta:(aux Expr.Meta.def)
      ~term_var:(fun _ _ -> assert false)
      ~term_meta:(aux Expr.Meta.def)

(** Split a single_cluster mapping according to meta indexes *)
let split_cluster map =
  let aux default meta t acc =
    let i = (meta.Expr.meta_index : Expr.meta_index :> int) in
    let s = N.get_or ~default i acc in
    N.add i (Mapping.Meta.bind_term s meta t) acc
  in
  let default = Mapping.keep ~ty_meta:(fun _ _ -> true) map in
  let tmp =
    Expr.Subst.fold (aux default)
      (Mapping.term_meta map) N.empty
  in
  List.map snd (N.bindings tmp)

let check_single_cluster m =
  let aux pp def m _ acc =
    match get_cluster (def m.Expr.meta_index) with
    | None -> assert false
    | Some (Root f)
    | Some (Under (f, _)) ->
      begin match acc with
        | None -> Some f
        | Some quant ->
          if Expr.Formula.equal quant f then acc
          else begin
            Util.warn ~section "@[<hv 2>Not a single cluster:@ %a@ %a@ %a@]"
              pp m Expr.Formula.print f Expr.Formula.print quant;
            raise Exit
          end
      end
  in
  try
    let _ = Mapping.fold m
        ~ty_meta:(aux Expr.Print.meta Expr.Meta.def)
        ~term_meta:(aux Expr.Print.meta Expr.Meta.def) in
    true
  with Exit -> false

(** Returns the formula defining a mapping (where all metas
    are assumed to be defined by the same formula or contiguous
    quantifications (i.e same cluster). *)
let map_def map =
  let res =
    try
      let m, _ = Expr.Subst.choose (Mapping.ty_meta map) in
      Expr.Meta.def m.Expr.meta_index
    with Not_found ->
      begin try
          let m, _ = Expr.Subst.choose (Mapping.term_meta map) in
          Expr.Meta.def m.Expr.meta_index
        with Not_found ->
          Util.debug ~section "Invalid subst: %a" Mapping.print map;
          raise (Invalid_argument "Inst.map_def")
      end
  in
  assert (check_single_cluster map);
  res

(* Partition caching *)
let partition_cache = Hm.create 4013

(* Expand a virtual meta cluster *)
let rec expand m =
  let f = map_def m in
  match Expr.Formula.get_tag f v_meta with
  | None -> [m]
  | Some s ->
    Util.debug ~section "@[<hv 2>expanding:@ %a@ with@ %a@]"
      Mapping.print m Mapping.print s;
    partition (Mapping.apply m s)

(* Given an arbitrary mapping,
 * returns a list of pairs (formula * mapping) to instanciate
 * the outermost metas in the given mapping. *)
and partition m =
  try
    Hm.find partition_cache m
  with Not_found ->
    Util.debug ~section "@[<hv 2>partition@ %a@]" Mapping.print m;
    let l = split m in
    Util.debug ~section "@[<hv 2>partition split:@ %a@]"
      CCFormat.(list ~sep:(return "@ ") Mapping.print) l;
    let l = List.map reduce_map l in
    Util.debug ~section "@[<hv 2>partition min split:@ %a@]"
      CCFormat.(list ~sep:(return "@ ") Mapping.print) l;
    let l = CCList.flat_map split_cluster l in
    Util.debug ~section "@[<hv 2>partition reduced split:@ %a@]"
      CCFormat.(list ~sep:(return "@ ") Mapping.print) l;
    let l = CCList.flat_map expand l in
    Util.debug ~section "@[<hv 2>partition result:@ %a@]"
      CCFormat.(list ~sep:(return "@ ") Mapping.print) l;
    let () = Hm.add partition_cache m l in
    l

(* Produces a proof for the instanciation of the given formulas and unifiers *)
let mk_proof ~name f q t tys ts =
  Dispatcher.mk_proof "inst" name (Inst (Formula (f, t, q, tys, ts)))

let to_var s =
  Mapping.fold
    ~ty_var:(fun _ _ _ -> assert false)
    ~ty_meta:(fun {Expr.meta_id = v} t acc -> Mapping.Var.bind_ty acc v t)
    ~term_var:(fun _ _ _ -> assert false)
    ~term_meta:(fun {Expr.meta_id = v} t acc -> Mapping.Var.bind_term acc v t)
    s Mapping.empty

let soft_subst ~name f t =
  let ty_subst = Mapping.ty_var t in
  let term_subst = Mapping.term_var t in
  let tys, ts =
    let l, _ = Mapping.codomain t in
    let l', _ = Mapping.domain t in
    Expr.Id.remove_fv l l'
  in
  Util.debug ~section "@[<hv 2>soft_subst:@ %a;@ %a"
    CCFormat.(list ~sep:(return ",@ ") Expr.Print.id) tys
    CCFormat.(list ~sep:(return ",@ ") Expr.Print.id) ts;
  let q =
    Expr.Formula.all (tys, ts) @@
    Expr.Formula.partial_inst ty_subst term_subst f
  in
  let () =
    let _, (l, l') = Mapping.codomain t in
    match indexes l l' with
    | [] -> ()
    | [i] -> mark_meta (Expr.Meta.def i) q
    | _ -> assert false
  in
  [ Expr.Formula.neg f; q], mk_proof ~name f q t tys ts

(* Heap for prioritizing instanciations *)
(* ************************************************************************ *)

module Inst = struct
  type t = {
    age   : int;
    hash  : int;
    score : int;
    name  : string;
    formula : Expr.formula;
    var_subst : Mapping.t;
  }

  (* Age counter *)
  let age = ref 0
  let clock () = incr age

  (* Constructor *)
  let mk_aux name score formula var_subst hash =
    { age = !age; hash; score; name; formula; var_subst; }

  let mk name u score =
    let formula = map_def u in
    let var_subst = to_var u in
    let hash = Hashtbl.hash (Expr.Formula.hash formula, Mapping.hash u) in
    mk_aux name score formula var_subst hash

  (* debug printing *)
  let print fmt t =
    Format.fprintf fmt "@[<hov 2>%a@ %a@]"
      Expr.Formula.print t.formula Mapping.print t.var_subst

  (* Comparison for the Heap *)
  let leq t1 t2 = t1.score + t1.age <= t2.score + t2.age

  (* Hash and equality for the hashtbl. *)
  let hash t = t.hash

  let equal t t' =
    Expr.Formula.equal t.formula t'.formula &&
    Mapping.equal t.var_subst t'.var_subst

end

module Q = CCHeap.Make(Inst)
module H = Hashtbl.Make(Inst)

let heap = ref Q.empty
let delayed = ref []
let inst_set = H.create 4096
let inst_incr = ref 0

let add_aux ~delay ~score t =
  if not (H.mem inst_set t) then begin
    H.add inst_set t false;
    Util.debug ~section "New inst /%d (%d):@ %a" score delay Inst.print t;
    if delay <= 0 then
      heap := Q.add !heap t
    else
      delayed := (t, delay) :: !delayed;
    true
  end else begin
    Util.debug ~section "Redondant inst:@ %a" Inst.print t;
    false
  end

let force ?(name="partial") ?(delay=0) ?(score=0) formula var_subst =
  let hash = Hashtbl.hash (Expr.Formula.hash formula, Mapping.hash var_subst) in
  let t = Inst.mk_aux name score formula var_subst hash in
  add_aux ~delay ~score t

let add ?(name="partial") ?(delay=0) ?(score=0) u =
  assert (match split_cluster (reduce_map u) with
      | [s] -> Mapping.equal s u
      | _ -> false);
  let t = Inst.mk name u score in
  add_aux ~delay ~score t

let push acc inst =
  assert (not (H.find inst_set inst));
  H.replace inst_set inst true;
  let open Inst in
  Util.debug ~section "Pushing inst:@ %a" Inst.print inst;
  let cl, p = soft_subst ~name:inst.name inst.formula inst.var_subst in
  Dispatcher.push cl p;
  acc + 1

let decr_delay () =
  if !delayed = [] then
    false
  else begin
    delayed := CCList.filter_map (fun (u, d) ->
        if d > 1 then begin
          Util.debug ~section "Decreased delay (%d):@ %a"
            (d - 1) Inst.print u;
          Some (u, d - 1)
        end else begin
          Util.debug ~section "Promoted inst:@ %a"
            Inst.print u;
          heap := Q.add !heap u;
          None
        end
      ) !delayed;
    true
  end

let inst_aux f acc k =
  let rec fold f acc i =
    if i <= 0 then
      if acc <= 0 && decr_delay () then
        fold f acc i
      else
        acc
    else begin
      match Q.take !heap with
      | None ->
        if decr_delay () then
          fold f acc i
        else
          fold f acc (i - 1)
      | Some (new_h, min) ->
        heap := new_h;
        fold f (f acc min) (i - 1)
    end
  in
  if k > 0 then begin
    Util.debug ~section "Folding over %d insts" k;
    fold f acc k
  end else begin
    Util.debug ~section "Folding over %d insts" (Q.size !heap + k);
    fold f acc (max 1 (Q.size !heap + k))
  end

let inst_sat () =
  Util.info ~section "Treating instanciations (k=%d)" !inst_incr;
  let n = inst_aux push 0 !inst_incr in
  Ext_stats.inst_remaining (Q.size !heap + List.length !delayed);
  Ext_stats.inst_done n;
  Inst.clock ();
  if n > 0 then
    Some (Solver.Assume [])
  else
    Some Solver.Sat_ok

(* Proof management *)
(* ************************************************************************ *)

let dot_info = function
  | Formula (f, t, _, _, _) ->
    Some "RED", [
      CCFormat.const Dot.Print.mapping t;
      CCFormat.const Dot.Print.formula f;
    ]
(*
let coq_destruct ctx fmt = function
  | { Expr.formula = Expr.Not ({
      Expr.formula = Expr.Ex(l, _, _)} as q)} ->
    let o = Expr.L (List.rev @@ (Expr.F (`Quant q)) ::
                                List.rev_map (fun x -> Expr.F (`Var x)) l) in
    let pp fmt = function
      | `Var x -> Coq.Print.id fmt x
      | `Quant q -> Proof.Ctx.named ctx fmt q
    in
    Format.fprintf fmt "destruct %a as %a.@ "
      (Proof.Ctx.named ctx) q (Coq.Print.pattern_ex pp) o
  | _ -> ()

let coq_inst_ex m cur fmt x =
  let t = match Mapping.Var.get_term_opt m x with
    | None -> Expr.Term.of_id x
    | Some t -> t
  in
  Format.fprintf fmt
    "(Coq.Logic.Classical_Pred_Type.not_ex_all_not _ _ %s) %a"
    cur Coq.Print.term t

let coq_proof = function
  | Formula ({ Expr.formula = Expr.All (l, _, _) } as f, t, q) ->
    Coq.tactic ~prefix:"Q" ~normalize:(Coq.Mem [f]) (fun fmt ctx ->
        let l', l'' = List.fold_left (fun (vars, args) x ->
            match Mapping.Var.get_term_opt t x with
            | None -> x :: vars, Expr.Term.of_id x :: args
            | Some t -> vars, t :: args) ([], []) l in
        let vars = List.rev l' in
        let args = List.rev l'' in
        begin match vars with
          | [] ->
            Coq.exact fmt "%a (%a)"
              (Proof.Ctx.named ctx) (Expr.Formula.neg q)
              (Coq.app_t ctx) (f, args)
          | _ ->
            Coq.exact fmt "%a (fun %a => %a)"
              (Proof.Ctx.named ctx) (Expr.Formula.neg q)
              Coq.fun_binder vars (Coq.app_t ctx) (f, args)
        end)
  | Formula ({ Expr.formula = Expr.Not (
      { Expr.formula = Expr.Ex (l, _, _) })} as f', t, q) ->
    Coq.tactic ~prefix:"Q" ~normalize:Coq.All
      ~prelude:[Coq.Prelude.classical] (fun fmt ctx ->
        (** Destruct the goal *)
        let () = coq_destruct ctx fmt q in
        let s = Coq.sequence ctx (coq_inst_ex t) (Proof.Ctx.name ctx f') fmt l in
        Coq.exact fmt "%s %a" s (Proof.Ctx.named ctx) (Expr.Formula.neg q)
      )
  | _ -> assert false
*)
(* Extension registering *)
(* ************************************************************************ *)

let handle : type ret. ret Dispatcher.msg -> ret option = function
  | Dot.Info Inst info -> Some (dot_info info)
  (* | Coq.Tactic Inst info -> Some (coq_proof info) *)
  | Solver.Found_sat _ -> inst_sat ()
  | _ -> None

let opts =
  let docs = Options.ext_sect in
  let n_of_inst =
    let doc = "Decides how many instanciations are pushed to the solver each round.
                   If $(docv) is a strictly positive number, then at each round, the $(docv)
                   most promising instanciations are pushed. If $(docv) is negative, then all
                   but the $(docv) least promising instanciations are pushed." in
    Cmdliner.Arg.(value & opt int 15 & info ["inst.nb"] ~docv:"N" ~docs ~doc)
  in
  let set_opts nb =
    inst_incr := nb
  in
  Cmdliner.Term.(pure set_opts $ n_of_inst)

let register () =
  Dispatcher.Plugin.register "inst" ~prio:5 ~options:opts
    ~descr:"Handles the pushing of clauses corresponding to instanciations. This plugin does not
          do anything by itself, but rather is called by other plugins when doing instanciations."
    (Dispatcher.mk_ext ~section ~handle:{Dispatcher.handle} ())

