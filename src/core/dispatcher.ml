
let section = Util.Section.make "dispatch"

let dummy_section = Util.Section.make "DUMMY"

(* Type definitions *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Term)
module M = Backtrack.HashtblBack(Expr.Term)
module F = Backtrack.HashtblBack(Expr.Formula)

type term = Expr.term
type formula = Expr.formula

type lemma = {
  plugin_name : string;
  proof_name : string;
  proof_ty_args : Expr.ty list;
  proof_term_args : Expr.term list;
  proof_formula_args : Expr.formula list;
}

type proof = lemma

type assumption =
  | Lit of formula
  | Assign of term * term

type slice = {
  start : int;
  length : int;
  get : int -> assumption * int;
  push : formula list -> proof -> unit;
  propagate : formula -> int -> unit;
}

type level = Backtrack.Stack.level

type res =
  | Sat
  | Unsat of formula list * proof

type eval_res =
  | Valued of bool * int
  | Unknown

type 'a job = {
  job_ext : 'a;
  job_n : int;
  job_section : Util.Section.t;
  job_callback : unit -> unit;
  job_formula : formula option;
  mutable job_done : int;
  mutable watched : term list;
  mutable not_watched : term list;
}

(* Exceptions *)
(* ************************************************************************ *)

exception Absurd of formula list * proof
exception Bad_assertion of string

let _fail s = raise (Bad_assertion s)

let profile section f = fun x ->
  Util.enter_prof section;
  try
    let res = f x in
    Util.exit_prof section;
    res
  with Absurd _ as e ->
    Util.exit_prof section;
    raise e

(* Extensions *)
(* ************************************************************************ *)

type ext = {
  (* Section for the extension (used for profiling) *)
  section : Util.Section.t;

  (* Called once on each new formula *)
  peek : (formula -> unit) option;

  (* Called at the end of each round of solving *)
  if_sat : (((formula -> unit) -> unit) -> unit) option;

  (* Called on each formula that the solver assigns to true *)
  assume : (formula * int -> unit) option;

  (* Evaluate a formula with the current assignments *)
  eval_pred : (formula -> (bool * int) option) option;

  (* Pre-process input formulas *)
  preprocess : (formula -> (formula * lemma) option) option;
}

let mk_ext ~section ?peek ?if_sat ?assume ?eval_pred ?preprocess () = {
  section;
  peek = CCOpt.map (profile section) peek;
  if_sat = CCOpt.map (profile section) if_sat;
  assume = CCOpt.map (profile section) assume;
  eval_pred =CCOpt.map (profile section) eval_pred;
  preprocess = CCOpt.map (profile section) preprocess;
}

let merge_opt merge o1 o2 = match o1, o2 with
  | None, res | res, None -> res
  | Some a, Some b -> Some (merge a b)

(* merge: iter on functions *)
let merge_iter a b = merge_opt (fun f f' -> (function arg -> f arg; f' arg)) a b

(* merge: eval functions and stop on the first non-None result *)
let merge_first a b =
  merge_opt (fun f f' ->
      (function arg ->
        match f arg with
        | (Some _) as res -> res
        | None -> f' arg
      )) a b

let merge_preprocess f p =
  match f, p with
  | None, res | res, None -> res
  | Some f', Some p' ->
    Some (function formula -> match f' formula with
        | None -> p' formula
        | Some (formula', _) -> p' formula')

let merge_exts l =
  let peek = List.fold_left (fun f r -> merge_iter f r.peek) None l in
  let if_sat = List.fold_left (fun f r -> merge_iter f r.if_sat) None l in
  let assume = List.fold_left (fun f r -> merge_iter f r.assume) None l in
  let eval_pred = List.fold_left (fun f r -> merge_first f r.eval_pred) None l in
  let preprocess = List.fold_left (fun f r -> merge_preprocess f r.preprocess) None l in
  { section = dummy_section; peek; if_sat; assume; eval_pred; preprocess; }

module Plugin = Extension.Make(struct
    type t = ext
    let dummy = mk_ext ~section ()
    let merge = merge_exts
    let section = Util.Section.make ~parent:section "plugins"
  end)

(* Proof management *)
(* ************************************************************************ *)

let mk_proof plugin_name ?(ty_args=[]) ?(term_args=[]) ?(formula_args=[]) name = {
  plugin_name;
  proof_name = name;
  proof_ty_args = ty_args;
  proof_term_args = term_args;
  proof_formula_args = formula_args;
}

let proof_debug p =
  let color = match p.proof_name with
    | "inst" -> Some "PURPLE"
    | "tab" -> Some "LIGHTBLUE"
    | _ -> None
  in
  p.proof_name, p.proof_formula_args, p.proof_term_args, color

(* Delayed propagation *)
(* ************************************************************************ *)

let push_stack = Stack.create ()
let propagate_stack = Stack.create ()

let push clause ext_name =
  Stack.push (clause, ext_name) push_stack

let propagate f lvl =
  Stack.push (f, lvl) propagate_stack

let do_propagate propagate =
  while not (Stack.is_empty propagate_stack) do
    let (t, lvl) = Stack.pop propagate_stack in
    Util.debug ~section 10 "Propagating : %a" Expr.Debug.formula t;
    propagate t lvl
  done

let do_push f =
  while not (Stack.is_empty push_stack) do
    let (a, p) = Stack.pop push_stack in
    Util.debug ~section 2 "Pushing '%s' : %a" p.proof_name (CCPrint.list ~sep:" || " Expr.Debug.formula) a;
    f a p
  done

(* Pre-processing *)
(* ************************************************************************ *)

let check_var v =
  if not (Expr.Id.is_interpreted v) && not (Expr.Id.is_assignable v) then
    Util.debug ~section 0 "WARNING: Variable %a is neither interpreted nor assignable" Expr.Debug.id v

let rec check_term = function
  | { Expr.term = Expr.Var v } -> check_var v
  | { Expr.term = Expr.Meta m } -> check_var Expr.(m.meta_id)
  | { Expr.term = Expr.App (p, _, l)} as t ->
    if not (Expr.(Ty.equal t.t_type Ty.prop) && l = []) then
      check_var p;
    List.iter check_term l

let check = function
  | { Expr.formula = Expr.Equal (a, b) } ->
    check_term a;
    check_term b
  | { Expr.formula = Expr.Pred p } ->
    check_term p
  | _ -> ()

let peek_at f = match (Plugin.get_res ()).peek with
  | Some peek -> peek f; check f
  | None -> ()

let pre_process f =
  Util.enter_prof section;
  Util.debug ~section 5 "  %a" Expr.Debug.formula f;
  Util.debug ~section 5 "Pre-processing :";
  let f' = match (Plugin.get_res ()).preprocess with
    | None -> f
    | Some processor -> begin match processor f with
        | None -> f
        | Some (f', _) -> f'
      end
  in
  Util.debug ~section 5 "  %a" Expr.Debug.formula f';
  Util.exit_prof section;
  f'

(* Backtracking *)
(* ************************************************************************ *)

let stack = Backtrack.Stack.create (
    Util.Section.make ~parent:section "backtrack")

let dummy = Backtrack.Stack.dummy_level

let last_backtrack = ref 0

let current_level () = Backtrack.Stack.level stack

let backtrack lvl =
  Util.debug ~section 10 "Backtracking";
  incr last_backtrack;
  Stack.clear propagate_stack;
  Backtrack.Stack.backtrack stack lvl

(* Current asusmptions *)
(* ************************************************************************ *)

(* The map of formula that are currently true *)
let f_map = F.create stack

let is_true f = F.mem f_map f

let add_assumption = F.add f_map

(* Evaluation/Watching functions *)
(* ************************************************************************ *)

(* The current assignment map, term -> value *)
let eval_map = M.create stack
(* Map of terms watched by extensions *)
let watchers = H.create 4096
let watch_map = H.create 4096

(* Exceptions *)
exception Not_assigned of term

(* Convenience function *)
let hpop assoc key =
  let res = H.find assoc key in
  H.remove assoc key;
  res

let is_assigned t =
  try ignore (M.find eval_map t); true with Not_found -> false

let get_assign t =
  try M.find eval_map t with Not_found -> raise (Not_assigned t)

let add_job job t =
  let l = try H.find watch_map t with Not_found -> [] in
  H.replace watch_map t (job :: l)

let call_job j =
  if CCOpt.(get true (map is_true j.job_formula))
     && j.job_done < !last_backtrack then begin
    j.job_done <- !last_backtrack;
    profile j.job_section j.job_callback ()
  end

let update_watch x j =
  let rec find p acc = function
    | [] -> raise Not_found
    | y :: r when p y -> y, List.rev_append r acc
    | y :: r -> find p (y :: acc) r
  in
  try
    let _, old_watched = find (Expr.Term.equal x) [] j.watched in
    try
      let y, old_not_watched = find (fun y -> not (is_assigned y)) [] j.not_watched in
      Util.debug ~section 10 "New watcher (%a) for job from %s"
        Expr.Debug.term y Plugin.((get j.job_ext).name);
      j.not_watched <- x :: old_not_watched;
      j.watched <- y :: old_watched;
      add_job j y
    with Not_found ->
      add_job j x;
      Util.debug ~section 10 "Calling job from %s" Plugin.((get j.job_ext).name);
      call_job j
  with Not_found ->
    let ext = Plugin.get j.job_ext in
    Util.debug ~section 0 "Error for job from %s, looking for %d, called by %a" ext.Plugin.name j.job_n Expr.Debug.term x;
    Util.debug ~section 0 "watched : %a" (CCPrint.list ~sep:" || " Expr.Debug.term) j.watched;
    Util.debug ~section 0 "not_watched : %a" (CCPrint.list ~sep:" || " Expr.Debug.term) j.not_watched;
    assert false

let new_job ?formula id k section watched not_watched f =
  Util.Stats.incr section Util.Stats.watchers;
  {
  job_ext = id;
  job_n = k;
  job_section = section;
  watched = watched;
  job_formula = formula;
  not_watched = not_watched;
  job_callback = f;
  job_done = - 1;
  }

let watch ?formula ext_name k args f =
  let plugin = Plugin.find ext_name in
  let section = Plugin.(plugin.ext.section) in
  let tag = Plugin.(plugin.id) in
  List.iter Expr.Term.eval args;
  assert (k > 0);
  let rec split assigned not_assigned i = function
    | l when i <= 0 ->
      let j = new_job ?formula tag k section not_assigned (List.rev_append l assigned) f in
      List.iter (add_job j) not_assigned
    | [] (* i > 0 *) ->
      let l = List.rev_append not_assigned assigned in
      let to_watch, not_watched = CCList.split k l in
      let j = new_job ?formula tag k section to_watch not_watched f in
      List.iter (add_job j) to_watch;
      call_job j
    | y :: r ->
      if is_assigned y then
        split (y :: assigned) not_assigned i r
      else
        split assigned (y :: not_assigned) (i - 1) r
  in
  let t' = Builtin.Misc.tuple args in
  let l = try H.find watchers t' with Not_found -> [] in
  if not (List.mem tag l) then begin
    Util.debug ~section 10 "New watch from %s, %d among : %a" Plugin.((get tag).name) k (CCPrint.list ~sep:" || " Expr.Debug.term) args;
    H.add watchers t' (tag :: l);
    split [] [] k (List.sort_uniq Expr.Term.compare args)
  end

let rec assign_watch t = function
  | [] -> Util.exit_prof section
  | j :: r ->
    begin
      try
        update_watch t j
      with Absurd _ as e ->
        List.iter (fun job -> add_job job t) r;
        Util.exit_prof section;
        raise e
    end;
    assign_watch t r

and set_assign t v lvl =
  Util.enter_prof section;
  try
    let v', lvl' = M.find eval_map t in
    Util.debug ~section 5 "Assigned (%d) : %a -> %a / %a" lvl' Expr.Debug.term t Expr.Debug.term v' Expr.Debug.term v;
    if not (Expr.Term.equal v v') then
      _fail "Incoherent assignments";
    Util.exit_prof section
  with Not_found ->
    Util.debug ~section 5 "Assign (%d) : %a -> %a" lvl Expr.Debug.term t Expr.Debug.term v;
    M.add eval_map t (v, lvl);
    let l = try hpop watch_map t with Not_found -> [] in
    Util.debug ~section 10 " Found %d watchers" (List.length l);
    assign_watch t l

let model () = M.fold eval_map (fun t (v, _) acc -> (t, v) :: acc) []

(* Mcsat Plugin functions *)
(* ************************************************************************ *)

let assume s =
  Util.enter_prof section;
  Util.debug ~section 5 "New slice of length %d" s.length;
  try
    for i = s.start to s.start + s.length - 1 do
      match s.get i with
      | Lit f, lvl ->
        Util.debug ~section 1 " Assuming (%d) %a" lvl Expr.Debug.formula f;
        add_assumption f lvl;
        begin match (Plugin.get_res ()).assume with
          | Some assume -> assume (f, lvl)
          | None -> ()
        end
      | Assign (t, v), lvl ->
        Util.debug ~section 1 " Assuming (%d) %a -> %a" lvl Expr.Debug.term t Expr.Debug.term v;
        set_assign t v lvl
    done;
    Util.exit_prof section;
    Util.debug ~section 8 "Propagating (%d)" (Stack.length propagate_stack);
    do_propagate s.propagate;
    do_push s.push;
    Sat
  with Absurd (l, p) ->
    Util.debug ~section 3 "Conflict '%s'" p.proof_name;
    List.iter (fun f -> Util.debug ~section 1 " |- %a" Expr.Debug.formula f) l;
    Util.exit_prof section;
    Unsat (l, p)

let if_sat_iter s f =
  for i = s.start to s.start + s.length - 1 do
    match s.get i with
    | Lit g, _ -> f g
    | _ -> ()
  done

let if_sat s =
  Util.enter_prof section;
  Util.debug ~section 0 "Iteration with complete model";
  begin try
      match (Plugin.get_res ()).if_sat with
      | Some if_sat -> if_sat (if_sat_iter s)
      | None -> ()
    with Absurd _ -> assert false
  end;
  Util.exit_prof section;
  do_push s.push

let assign t =
  Util.enter_prof section;
  Util.debug ~section 5 "Finding assignment for %a" Expr.Debug.term t;
  try
    let res = Expr.Term.assign t in
    Util.debug ~section 5 " -> %a" Expr.Debug.term res;
    Util.exit_prof section;
    res
  with Expr.Cannot_assign _ ->
    _fail (CCPrint.sprintf
             "Expected to be able to assign symbol %a\nYou may have forgotten to activate an extension" Expr.Debug.term t)

let rec iter_assign_aux f e = match Expr.(e.term) with
  | Expr.App (p, _, l) ->
    if Expr.Id.is_assignable p then f e;
    List.iter (iter_assign_aux f) l
  | _ -> f e

let iter_assignable f e =
  Util.enter_prof section;
  Util.debug ~section 5 "Iter_assign on %a" Expr.Debug.formula e;
  peek_at e;
  begin match Expr.(e.formula) with
    | Expr.Equal (a, b) -> iter_assign_aux f a; iter_assign_aux f b
    | Expr.Pred p -> iter_assign_aux f p
    | _ -> ()
  end;
  Util.exit_prof section

let eval_aux f =
  match (Plugin.get_res ()).eval_pred with
  | None -> Unknown
  | Some eval_pred -> begin match eval_pred f with
      | None -> Unknown
      | Some (b, lvl) -> Valued (b, lvl)
    end

let eval formula =
  Util.enter_prof section;
  Util.debug ~section 5 "Evaluating formula : %a" Expr.Debug.formula formula;
  let res = eval_aux formula in
  Util.exit_prof section;
  res


