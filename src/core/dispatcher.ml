
let log_section = Util.Section.make "dispatch"
let log i fmt = Util.debug ~section:log_section i fmt

(* Type definitions *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Expr.Term)
module M = Backtrack.HashtblBack(Expr.Term)
module I = Backtrack.HashtblBack(struct type t = int let equal i j = i=j let hash i = i land max_int end)

type id = int
type term = Expr.term
type formula = Expr.formula
type lemma = {
  proof_ext : id;
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

type job = {
  job_ext : id;
  job_n : int;
  mutable job_done : int;
  job_callback : unit -> unit;
  mutable watched : term list;
  mutable not_watched : term list;
}

(* Proof management *)
(* ************************************************************************ *)

let mk_proof ?(ty_args=[]) ?(term_args=[]) ?(formula_args=[]) id name = {
  proof_ext = id;
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

(* Exceptions *)
(* ************************************************************************ *)

exception Absurd of formula list * proof
exception Bad_assertion of string
exception Extension_not_found of string

let _fail s = raise (Bad_assertion s)

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
    log 10 "Propagating : %a" Expr.Debug.formula t;
    propagate t lvl
  done

let do_push f =
  while not (Stack.is_empty push_stack) do
    let (a, p) = Stack.pop push_stack in
    log 2 "Pushing '%s' : %a" p.proof_name (CCPrint.list ~sep:" || " Expr.Debug.formula) a;
    f a p
  done

(* Extensions *)
(* ************************************************************************ *)

type extension = {
  (* Extension description *)
  id : id;
  prio : int;
  name : string;
  descr : string;

  (* Called once on each new formula *)
  peek : (formula -> unit) option;

  (* Called at the end of each round of solving *)
  if_sat : (((formula -> unit) -> unit) -> unit) option;

  (* Called on each formula that the solver assigns to true *)
  assume : (formula * int -> unit) option;

  (* Evaluate a formula with the current assignments *)
  eval_pred : (formula -> (bool * int) option) option;

  (* Pre-process input formulas *)
  preprocess : (formula -> (formula * proof) option) option;

  (* Add options to the command line utility *)
  options : Options.copts Cmdliner.Term.t -> Options.copts Cmdliner.Term.t;
}

let mk_ext ?(descr="") ?(prio=0)
    ?peek ?if_sat ?assume
    ?eval_pred ?preprocess
    ?(options=(fun t -> t))
    id name =
      { id; prio; name; descr; peek; if_sat; assume; eval_pred; preprocess; options; }

let actual = ref (mk_ext ~-1 "actual")

let extensions = CCVector.create ()
let active = ref []

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

(* merge: fold *)

let set_actual () =
  let peek = List.fold_left (fun f r -> merge_iter f r.peek) None !active in
  let if_sat = List.fold_left (fun f r -> merge_iter f r.if_sat) None !active in
  let assume = List.fold_left (fun f r -> merge_iter f r.assume) None !active in
  let eval_pred = List.fold_left (fun f r -> merge_first f r.eval_pred) None !active in
  let options = List.fold_left (fun f r -> (fun arg -> r.options @@ f arg)) (fun t -> t) !active in
  actual := mk_ext ?peek ?if_sat ?assume ?eval_pred ~options ~-1 "actual"

(* Info about extensions *)
let list_extensions () = CCVector.fold (fun acc r -> r.name :: acc) [] extensions

let doc_of_ext r = `I ("$(b," ^ r.name ^ ")", r.descr)

let ext_doc () =
  List.map doc_of_ext @@
  List.sort (fun r r' -> compare r.name r'.name) @@
  CCVector.to_list extensions

let find_ext id = CCVector.get extensions id

let add_opts t = CCVector.fold (fun t r -> r.options t) t extensions

(* Adding new extensions *)
(* ************************************************************************ *)

let new_id () =
  let i = CCVector.length extensions in
  CCVector.push extensions (mk_ext i "dummy");
  i

let register r =
  assert (not (CCVector.exists (fun r' -> r'.name = r.name) extensions));
  CCVector.set extensions r.id r

let activate ext =
  let aux r = r.name = ext in
  try
    let r = CCVector.find_exn aux extensions in
    if not (List.exists aux !active) then begin
      active := List.merge (fun r r' -> compare r'.prio r.prio) [r] !active;
      set_actual ()
    end else
      log 0 "WARNING: Extension %s already activated" ext
  with Not_found ->
    raise (Extension_not_found ext)

let deactivate ext =
  let aux r = r.name = ext in
  try
    if not (CCVector.exists aux extensions) then
      raise (Extension_not_found ext);
    let l1, l2 = List.partition aux !active in
    begin match l1 with
      | [] -> log 0 "WARNING: Extension %s already deactivated" ext
      | [r] ->
        active := l2;
        set_actual ()
      | _ -> assert false
    end
  with Not_found ->
    raise (Extension_not_found ext)

let set_ext s =
  if s <> "" then match s.[0] with
    | '-' -> deactivate (String.sub s 1 (String.length s - 1))
    | '+' -> activate (String.sub s 1 (String.length s - 1))
    | _ -> activate s

let set_exts s =
  List.iter set_ext
    (List.map (fun (s, i, l) -> String.sub s i l) (CCString.Split.list_ ~by:"," s))

let log_active () =
  log 0 "loaded extensions: %a" CCPrint.(list string) (List.map (fun r -> r.name) !active)

(* Pre-processing *)
(* ************************************************************************ *)

let check_var v =
  if not (Expr.Id.is_interpreted v) && not (Expr.Id.is_assignable v) then
    log 0 "WARNING: Variable %a is neither interpreted nor assignable" Expr.Debug.id v

let rec check_term = function
  | { Expr.term = Expr.Var v } -> check_var v
  | { Expr.term = Expr.Meta m } -> check_var Expr.(m.meta_id)
  | { Expr.term = Expr.App (p, _, l)} ->
    check_var p;
    List.iter check_term l

let rec check = function
  | { Expr.formula = Expr.Equal (a, b) } ->
    check_term a;
    check_term b
  | { Expr.formula = Expr.Pred p } ->
    check_term p
  | { Expr.formula = ( Expr.True | Expr.False ) } ->
    ()
  | { Expr.formula = Expr.Not f } ->
    check f
  | { Expr.formula = Expr.And l }
  | { Expr.formula = Expr.Or l } ->
    List.iter check l
  | { Expr.formula = Expr.Imply (p, q) }
  | { Expr.formula = Expr.Equiv (p, q) } ->
    check p;
    check q
  | { Expr.formula = Expr.All (_, _, f) }
  | { Expr.formula = Expr.AllTy (_, _, f) }
  | { Expr.formula = Expr.Ex (_, _, f) }
  | { Expr.formula = Expr.ExTy (_, _, f) } ->
    check f

let peek_at f = match !actual.peek with
  | Some peek -> peek f
  | None -> ()

let pre_process f = f
  (*
  let aux f r = match r.preprocess f with
    | None -> f
    | Some (f', _) -> f' (* TODO: register the proof *)
  in
  let f' = ext_fold aux f in
  log 5 "Pre-processing :";
  log 5 "  %a" Expr.Debug.formula f;
  log 5 "  %a" Expr.Debug.formula f';
  f'
     *)

(* Backtracking *)
(* ************************************************************************ *)

let stack = Backtrack.Stack.create ()

let dummy = Backtrack.Stack.dummy_level

let last_backtrack = ref 0

let current_level () = Backtrack.Stack.level stack

let backtrack lvl =
  log 10 "Backtracking";
  incr last_backtrack;
  Stack.clear propagate_stack;
  Backtrack.Stack.backtrack stack lvl

(* Evaluation/Watching functions *)
(* ************************************************************************ *)

(* The current assignment map, term -> value *)
let eval_map = M.create stack
(* Map of terms watching other terms, term -> list of terms to evaluate when arg has value *)
let wait_eval = M.create stack
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

(*
let add_wait_eval t t' =
  assert (not (is_assigned t));
  let l = try M.find wait_eval t' with Not_found -> [] in
  M.add wait_eval t' (List.sort_uniq Expr.Term.compare (t :: l))
*)

let add_job job t =
  let l = try H.find watch_map t with Not_found -> [] in
  H.replace watch_map t (job :: l)

let call_job j =
  if j.job_done < !last_backtrack then begin
    j.job_done <- !last_backtrack;
    j.job_callback ()
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
      log 10 "New watcher (%a) for job from %s" Expr.Debug.term y (find_ext j.job_ext).name;
      j.not_watched <- x :: old_not_watched;
      j.watched <- y :: old_watched;
      add_job j y
    with Not_found ->
      add_job j x;
      log 10 "Calling job from %s" (find_ext j.job_ext).name;
      call_job j
  with Not_found ->
    let ext = find_ext j.job_ext in
    log 0 "Error for job from %s, looking for %d, called by %a" ext.name j.job_n Expr.Debug.term x;
    log 0 "watched : %a" (CCPrint.list ~sep:" || " Expr.Debug.term) j.watched;
    log 0 "not_watched : %a" (CCPrint.list ~sep:" || " Expr.Debug.term) j.not_watched;
    assert false

let new_job id k watched not_watched f = {
  job_ext = id;
  job_n = k;
  watched = watched;
  not_watched = not_watched;
  job_callback = f;
  job_done = - 1;
}

let watch tag k args f =
  assert (k > 0);
  let rec split assigned not_assigned i = function
    | l when i <= 0 ->
      let j = new_job tag k not_assigned (List.rev_append l assigned) f in
      List.iter (add_job j) not_assigned
    | [] (* i > 0 *) ->
      let l = List.rev_append not_assigned assigned in
      let to_watch, not_watched = CCList.split k l in
      let j = new_job tag k to_watch not_watched f in
      List.iter (add_job j) to_watch;
      call_job j
    | y :: r ->
      if is_assigned y then
        split (y :: assigned) not_assigned i r
      else
        split assigned (y :: not_assigned) (i - 1) r
  in
  let t' = Builtin.tuple args in
  let l = try H.find watchers t' with Not_found -> [] in
  if not (List.mem tag l) then begin
    log 10 "New watch from %s, %d among : %a" (find_ext tag).name k (CCPrint.list ~sep:" || " Expr.Debug.term) args;
    H.add watchers t' (tag :: l);
    split [] [] k (List.sort_uniq Expr.Term.compare args)
  end

(*
let rec try_eval t =
  assert (not (is_assigned t));
  log 7 "Try-Eval of %a" Expr.Debug.term t;
  match Expr.(t.term) with
  | Expr.App (f, _, l) ->
    begin try
        begin match Expr.eval t with
          | Expr.Interpreted (v, lvl) ->
            set_assign t v lvl;
            Some v
          | Expr.Waiting t' ->
            begin match try_eval t' with
              | None -> add_wait_eval t t'; None
              | Some _ -> try_eval t
            end
        end
      with
      | Expr.Cannot_interpret _ -> None
    end
  | _ ->
    begin try
        Some (fst (get_assign t))
      with Not_assigned _ ->
        None
    end
*)

let rec assign_watch t = function
  | [] -> ()
  | j :: r ->
    begin
      try
        update_watch t j
      with Absurd _ as e ->
        List.iter (fun job -> add_job job t) r;
        raise e
    end;
    assign_watch t r

and set_assign t v lvl =
  try
    let v', lvl' = M.find eval_map t in
    log 5 "Assigned (%d) : %a -> %a / %a" lvl' Expr.Debug.term t Expr.Debug.term v' Expr.Debug.term v;
    if not (Expr.Term.equal v v') then
      _fail "Incoherent assignments"
  with Not_found ->
    log 5 "Assign (%d) : %a -> %a" lvl Expr.Debug.term t Expr.Debug.term v;
    M.add eval_map t (v, lvl);
    let l = try hpop watch_map t with Not_found -> [] in
    log 10 " Found %d watchers" (List.length l);
    assign_watch t l
    (*
    begin try
        let l = pop wait_eval t in
        log 10 " Waiting for %a :" Expr.Debug.term t;
        List.iter (fun t' -> log 10 "  -> %a" Expr.Debug.term t') l;
        List.iter (fun t' -> ignore (try_eval t')) l
      with Not_found -> () end
      *)

let model () = M.fold eval_map (fun t (v, _) acc -> (t, v) :: acc) []

(* Mcsat Plugin functions *)
(* ************************************************************************ *)

let assume s =
  log 5 "New slice of length %d" s.length;
  try
    for i = s.start to s.start + s.length - 1 do
      match s.get i with
      | Lit f, lvl ->
        log 1 " Assuming (%d) %a" lvl Expr.Debug.formula f;
        begin match !actual.assume with
          | Some assume -> assume (f, lvl)
          | None -> ()
        end
      | Assign (t, v), lvl ->
        log 1 " Assuming (%d) %a -> %a" lvl Expr.Debug.term t Expr.Debug.term v;
        set_assign t v lvl
    done;
    log 8 "Propagating (%d)" (Stack.length propagate_stack);
    do_propagate s.propagate;
    do_push s.push;
    Sat
  with Absurd (l, p) ->
    log 3 "Conflict '%s'" p.proof_name;
    List.iter (fun f -> log 1 " |- %a" Expr.Debug.formula f) l;
    Unsat (l, p)

let if_sat s =
  log 0 "Iteration with complete model";
  let iter f =
    for i = s.start to s.start + s.length - 1 do
      match s.get i with
      | Lit g, _ -> f g
      | _ -> ()
    done
  in
  begin try
      match !actual.if_sat with
      | Some if_sat -> if_sat iter
      | None -> ()
    with Absurd _ -> assert false
  end;
  do_push s.push

let assign t =
  log 5 "Finding assignment for %a" Expr.Debug.term t;
  try
    let res = Expr.Term.assign t in
    log 5 " -> %a" Expr.Debug.term res;
    res
  with Expr.Cannot_assign _ ->
    _fail (CCPrint.sprintf
             "Expected to be able to assign symbol %a\nYou may have forgotten to activate an extension" Expr.Debug.term t)

let rec iter_assign_aux f e = match Expr.(e.term) with
  | Expr.App (p, _, l) ->
    if not (Expr.Id.is_interpreted p) then f e;
    List.iter (iter_assign_aux f) l
  | _ -> f e

let iter_assignable f e =
  log 5 "Iter_assign on %a" Expr.Debug.formula e;
  peek_at e;
  match Expr.(e.formula) with
  | Expr.Equal (a, b) -> iter_assign_aux f a; iter_assign_aux f b
  | Expr.Pred p -> iter_assign_aux f p
  | _ -> ()

exception Found_eval of bool * int
let eval_aux f =
  match !actual.eval_pred with
  | None -> Unknown
  | Some eval_pred -> begin match eval_pred f with
      | None -> Unknown
      | Some (b, lvl) -> Valued (b, lvl)
    end

let eval formula =
  log 5 "Evaluating formula : %a" Expr.Debug.formula formula;
  eval_aux formula


