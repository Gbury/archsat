(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Log&Module Init *)
(* ************************************************************************ *)

let section = Section.make "synth"

module V = Hashtbl.Make(Expr.Id.TyCstr)
module H = Hashtbl.Make(Expr.Ty)
module S = Set.Make(Expr.Id.Const)
module T = CCSet.Make(Expr.Ty)


(* Timestamps *)
(* ************************************************************************ *)

let current, tick =
  let r = ref 0 in
  (fun () -> !r),
  (fun () -> incr r)

(* Helper functions *)
(* ************************************************************************ *)

let size term =
  let rec aux acc = function
    | { Expr.term = Expr.Var _ }
    | { Expr.term = Expr.Meta _ } -> 1
    | { Expr.term = Expr.App (_, _, l) } ->
      List.fold_left aux (acc + 1) l
  in
  aux 0 term

(* Association tables *)
(* ************************************************************************ *)

(* functions whose return type is a type variable *)
let poly_list = ref []
(* map each type constructor with a set of functions whose return type starts
   with that constructor. *)
let head_table = V.create 1013

let get_head f =
  try V.find head_table f
  with Not_found -> S.empty

let add_head f v =
  let s = get_head f in
  V.add head_table f (S.add v s)

let add_id v =
  Util.debug ~section "Adding: %a" Expr.Print.const_ty v;
  match Expr.(v.id_type.fun_ret) with
  | { Expr.ty = Expr.TyMeta _ } -> assert false
  | { Expr.ty = Expr.TyVar _ } -> poly_list := v :: !poly_list
  | { Expr.ty = Expr.TyApp (f, _) } -> add_head f v

let iter_on_head h =
  let s = get_head h in
  let l = !poly_list in
  (fun f ->
     let () = S.iter f s in
     List.iter f l
  )


(* Queues *)
(* ************************************************************************ *)

type node = {
  mutable timestamp : int;
  mutable descr : node_descr;
}

and node_descr =
  | Impossible
  | Find of Expr.ty
  | Done of Expr.term
  | Queue of queue

and queue = {
  goal : Expr.ty;
  mutable q : task list;
}

and task = {
  obj : Expr.ty;
  f : Expr.Id.Const.t;
  tys : Expr.ty list;
  args : node list;
}

let table : node H.t = H.create 1013

let rec pp_node fmt node =
  match node.descr with
  | Impossible ->
    Format.fprintf fmt "|+ Impossible"
  | Find ty ->
    Format.fprintf fmt "|+ Find{@[<hov>%a@]}" Expr.Ty.print ty
  | Done t ->
    Format.fprintf fmt "|+ Found{@[<hov>%a@]}" Expr.Term.print t
  | Queue q ->
    Format.fprintf fmt "|+ @[<v>Queue{@[<hov>%a@]}:@ %a@]"
      Expr.Ty.print q.goal CCFormat.(list ~sep:(return "@ ") pp_task) q.q

and pp_task fmt t =
  Format.fprintf fmt "|- @[<v>f: @[<hov>%a(%a)@]@ %a@]"
    Expr.Id.print t.f
    CCFormat.(list ~sep:(return ",@ ") Expr.Ty.print) t.tys
    CCFormat.(list ~sep:(return "@ ") pp_node) t.args

(* Synthetizing functions *)
(* ************************************************************************ *)

let mk_node h ty =
  if T.mem ty h then { timestamp = 0; descr = Impossible }
  else
    try H.find table ty
    with Not_found ->
      let res = { timestamp = current (); descr = Find ty } in
      H.add table ty res;
      res

let term_try ty h f =
  Util.debug ~section "Trying: %a" Expr.Print.const_ty f;
  match Match.ty Mapping.empty Expr.(f.id_type.fun_ret) ty with
  | exception Match.Impossible_ty _ ->
    Util.debug ~section "  \- unif failed";
    None
  | m ->
    Util.debug ~section "  \- unif found !";
    (* TODO: allow variables in types of terms to synthetize ? *)
    let m' = List.fold_left (fun acc v ->
        if Mapping.Var.mem_ty acc v then acc
        else Mapping.Var.bind_ty acc v Expr.Ty.base
      ) m Expr.(f.id_type.fun_vars) in
    let tys = List.map (Mapping.Var.get_ty m') Expr.(f.id_type.fun_vars) in
    let arg_tys = List.map (Mapping.apply_ty ~fix:false m') Expr.(f.id_type.fun_args) in
    Util.debug ~section "    @[<v 2>Need to look for:@ %a@]"
      CCFormat.(list ~sep:(return "@ ") Expr.Ty.print) arg_tys;
    assert (List.for_all Expr.Ty.is_ground arg_tys);
    let args = List.map (mk_node h) arg_tys in
    Some { obj = ty; f; tys; args }

let collapse goal = function
  | [] -> Impossible
  | l ->
    begin try
        let t = List.find (fun t -> t.args = []) l in
        let res = Expr.Term.apply t.f t.tys [] in
        assert (Expr.Ty.equal goal res.Expr.t_type);
        Done res
      with Not_found ->
        Queue { goal; q = l }
    end

let term_aux h ty =
  match ty with
  (* Type Variables and meta-variables shouldn't appear *)
  | { Expr.ty = Expr.TyVar _ } -> assert false
  | { Expr.ty = Expr.TyMeta _ } -> assert false
  (* Since type metas are replaced by Expr.Ty.base, this is sound *)
  (* Interesting case *)
  | { Expr.ty = Expr.TyApp (f, _) } as ty ->
    let l = CCFun.(
        iter_on_head f
        |> Sequence.filter_map (term_try ty h)
        |> Sequence.to_list) in
    collapse ty l

let rec perform h task =
  let () = List.iter (expand h) task.args in
  if List.exists (function { descr = Impossible; _ } -> true | _ -> false) task.args then
    Impossible
  else
    try
      let l = List.map (function
          | { descr = Done t ; _ } -> t
          | _ -> raise Exit
        ) task.args in
      let res = Expr.Term.apply task.f task.tys l in
      Done res
    with Exit -> Queue { goal = task.obj; q = [ task ] }

and merge acc = function
  | []                  -> `List acc
  | Done res      :: _  -> `Finished res
  | Impossible    :: r  -> merge acc r
  | Queue { q }   :: r  -> merge (q @ acc) r
  | Find _        :: _  -> assert false

and expand h node =
  if node.timestamp < current () then begin
    node.timestamp <- current ();
    match node.descr with
    | Done _ | Impossible -> ()
    | Find ty ->
      let h' = T.add ty h in
      let res = term_aux h' ty in
      node.descr <- res
    | Queue { goal; q } ->
      let h' = T.add goal h in
      let l = List.map (perform h') q in
      let res =
        match merge [] l with
        | `Finished t -> Done t
        | `List l -> Queue { goal; q = l }
      in
      node.descr <- res
  end

let rec find_term ty depth n =
  tick ();
  if depth <= 0 then begin
    Util.info ~section
      "@[<hv>Reached max depth while synthetizing term of type:@ @[<hov>%a@]@]"
      Expr.Ty.print ty
  end else begin
    let () = expand T.empty n in
    Util.debug "@[<v>after expansion:@ %a@]" pp_node n;
    match n.descr with
    | Done _ | Impossible -> ()
    | Find _ | Queue _    -> find_term ty (depth - 1) n
  end

(* API functions *)
(* ************************************************************************ *)

let ty = Expr.Ty.base

let remove_metas ty =
  match Expr.Ty.fm ty with
  | l, [] ->
    let m = List.fold_left (fun acc v ->
        Mapping.Meta.bind_ty acc v Expr.Ty.base
      ) Mapping.empty l in
    Mapping.apply_ty ~fix:false m ty
  | _ -> assert false

let synth_term =
  let w =
    let a = Expr.Id.ttype "a" in
    Expr.Id.term_fun "##w" [a] [] (Expr.Ty.of_id a)
  in
  (fun ty -> Expr.Term.apply w [ty] [])

let term_aux goal =
  Util.debug ~section "Trying to find a term of type: %a" Expr.Ty.print goal;
  let ty = remove_metas goal in
  Util.debug ~section "After removing metas: %a" Expr.Ty.print ty;
  Util.enter_prof section;
  assert (Expr.Ty.is_ground ty);
  let n = mk_node T.empty ty in
  let () = find_term ty 5 n in
  Util.exit_prof section;
  match n.descr with
  | Done t -> t
  | _ ->
    Util.warn ~section
      "@[<hv>Couldn't find a term of type@ @[<hov>%a@]@ (originally @[<hov>%a@])@\n%s@]"
      Expr.Ty.print ty Expr.Ty.print goal
      "The output proof will have some added some hypothesis to type-check";
    let t = synth_term ty in
    n.descr <- Done t;
    t

let term = Util.within_prof section term_aux

let register t =
  let ty = Expr.(t.t_type) in
  assert (Expr.Ty.fv ty = ([], []));
  let n = mk_node T.empty ty in
  n.descr <- Done t

