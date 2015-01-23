
let log_section = Util.Section.make "dispatch"
let log i fmt = Util.debug ~section:log_section i fmt

(* Type definitions *)
(* ************************************************************************ *)

module M = Backtrack.HashtblBack(Expr.Term)
module I = Backtrack.HashtblBack(struct type t = int let equal i j = i=j let hash i = i land max_int end)

type term = Expr.term
type formula = Expr.formula
type proof = int

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

(* Additional options *)
(* ************************************************************************ *)

let options = ref []
let get_options () = !options

(* Extensions registering *)
(* ************************************************************************ *)

exception Absurd of formula list
exception Bad_assertion of string
exception Extension_not_found of string

let _fail s = raise (Bad_assertion s)

type extension = {
  name : string;
  assume : formula * int -> unit;
  eval_pred : formula -> (bool * int) option;
  preprocess : formula -> unit;
}

let dummy_ext = {
  name = "";
  assume = (fun _ -> _fail "dummy ext used");
  eval_pred = (fun _ -> _fail "dummy ext used");
  preprocess = (fun _ -> _fail "dummy ext used");
}

let extensions = ref []

let active = Vector.make 10 dummy_ext

let register r =
  assert (not (List.exists (fun r' -> r'.name = r.name) !extensions));
  extensions := r :: !extensions

let register_options l =
  options := l @ !options

let activate ext =
  let aux r = r.name = ext in
  try
    let r = List.find aux !extensions in
    if not (Vector.exists aux active) then
      Vector.push active r
    else
      log 0 "WARNING: Extension %s already activated" r.name
  with Not_found ->
    raise (Extension_not_found ext)

let list_extensions () = List.map (fun r -> r.name) !extensions

(* Acces functions for active extensions *)
let ext_iter f = Vector.iter f active
let ext_iteri f = Vector.iteri f active

exception Found_ext of int
let find_ext name =
  try
    ext_iteri (fun i r -> if r.name = name then raise (Found_ext i));
    _fail (Util.sprintf "Expected to find %s in active extensions" name)
  with Found_ext i -> i

(* Pre-processing *)
(* ************************************************************************ *)

let check_var v =
  if not (Expr.is_interpreted v) && not (Expr.is_assignable v) then
    log 0 "WARNING: Variable %a is neither interpreted nor assignable" Expr.debug_var v

let rec check_term = function
  | { Expr.term = Expr.Var v } -> check_var v
  | { Expr.term = Expr.Meta m } -> check_var Expr.(m.meta_var)
  | { Expr.term = Expr.Tau t } -> check_var Expr.(t.tau_var)
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
  | { Expr.formula = Expr.All (_, f) }
  | { Expr.formula = Expr.AllTy (_, f) }
  | { Expr.formula = Expr.Ex (_, f) } ->
    check f

let preprocess f =
  ext_iter (fun r -> r.preprocess f);
  check f

(* Evaluation/Watching functions *)
(* ************************************************************************ *)

(* The global stack *)
let stack = Backtrack.Stack.create ()

(* The current assignment map, term -> value *)
let eval_map = M.create stack
(* Map of terms watching other terms, term -> list of terms to evaluate when arg has value *)
let wait_eval = M.create stack
(* Map of terms watched by extensions, term -> continuation list *)
let watch_map = M.create stack
let job_map = I.create stack

(* Exceptions *)
exception Not_assigned of term

(* Convenience function *)
let pop assoc key =
  let res = M.find assoc key in
  M.remove assoc key;
  res

let popi assoc key =
  let res = I.find assoc key in
  I.remove assoc key;
  res

let is_assigned t =
  try ignore (M.find eval_map t); true with Not_found -> false

let get_assign t =
  try M.find eval_map t with Not_found -> raise (Not_assigned t)

let add_wait_eval t t' =
  assert (not (is_assigned t));
  let l = try M.find wait_eval t' with Not_found -> [] in
  M.add wait_eval t' (List.sort_uniq Expr.Term.compare (t :: l))

let add_job job_id t =
  let l = try M.find watch_map t with Not_found -> [] in
  M.add watch_map t (List.sort_uniq compare (job_id :: l))

let set_job id job = I.add job_map id job

let update_watch x job_id =
  try
    let k, args, f = popi job_map job_id in
    let rec find not_assigned acc = function
      | [] -> f ()
      | y :: r when not (is_assigned y) ->
        let l = List.rev_append (y :: not_assigned) (x :: r) in
        set_job job_id (k, l, f)
      | y :: r -> find not_assigned (y :: acc) r
    in
    let rec split i acc = function
      | [] -> find acc [] []
      | l when i <= 0 -> find acc [] l
      | y :: r when Expr.Term.equal x y -> split (i - 1) acc r
      | y :: r -> split (i - 1) (y :: acc) r
    in
    split k [] args
  with Not_found ->
    ()

let rec try_eval t =
  assert (not (is_assigned t));
  log 7 "Try-Eval of %a" Expr.debug_term t;
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

and set_assign t v lvl =
  try
    let v', lvl' = M.find eval_map t in
    log 5 "Assigned (%d) : %a -> %a / %a" lvl' Expr.debug_term t Expr.debug_term v' Expr.debug_term v;
    if not (Expr.Term.equal v v') then
      _fail "Incoherent assignments"
  with Not_found ->
    log 5 "Assign (%d) : %a -> %a" lvl Expr.debug_term t Expr.debug_term v;
    M.add eval_map t (v, lvl);
    begin try
        let l = pop watch_map t in
        log 10 " Found %d watchers" (List.length l);
        List.iter (update_watch t) l
      with Not_found -> () end;
    begin try
        let l = pop wait_eval t in
        log 10 " Waiting for %a :" Expr.debug_term t;
        List.iter (fun t' -> log 10 "  -> %a" Expr.debug_term t') l;
        List.iter (fun t' -> ignore (try_eval t')) l
      with Not_found -> () end

let job_max = ref 0

let watch k args f =
  let rec split assigned not_assigned i = function
    | l when i <= 0 ->
      incr job_max;
      List.iter (add_job !job_max) not_assigned;
      let l = List.rev_append not_assigned (List.rev_append l assigned) in
      set_job !job_max (k, l, f)
    | [] (* i > 0 *) -> f ()
    | y :: r ->
      if is_assigned y then
        split (y :: assigned) not_assigned i r
      else
        split assigned (y :: not_assigned) (i - 1) r
  in
  split [] [] k args

let model () = M.fold eval_map (fun t (v, _) acc -> (t, v) :: acc) []

(* Delayed propagation *)
(* ************************************************************************ *)

let push_stack = ref []
let propagate_stack = ref []

let push clause ext_name =
  push_stack := (clause, find_ext ext_name) :: !push_stack

let propagate f lvl =
  propagate_stack := (f, lvl) :: !propagate_stack

let apply f l =
  List.iter (fun (a, b) -> f a b) !l;
  l := []

(* Mcsat Plugin functions *)
(* ************************************************************************ *)

let dummy = Backtrack.Stack.dummy_level

let current_level () = Backtrack.Stack.level stack

let backtrack lvl =
  log 10 "Backtracking";
  propagate_stack := [];
  Backtrack.Stack.backtrack stack lvl

exception Exit_unsat of formula list * int
let assume s =
  log 5 "New slice of length %d" s.length;
  try
    for i = s.start to s.start + s.length - 1 do
      match s.get i with
      | Lit f, lvl ->
        log 8 " Assuming (%d) %a" lvl Expr.debug_formula f;
        ext_iteri (fun j ext ->
            try
              ext.assume (f, lvl)
            with Absurd l ->
              raise (Exit_unsat (l, j)))
      | Assign (t, v), lvl -> set_assign t v lvl
    done;
    log 8 "Pushing (%d)" (List.length !push_stack);
    apply s.push push_stack;
    log 8 "Propagating (%d)" (List.length !propagate_stack);
    apply s.propagate propagate_stack;
    Sat
  with Exit_unsat (l, j) ->
    Unsat (l, j)

let assign t =
  log 5 "Finding assignment for %a" Expr.debug_term t;
  try
    let res = Expr.assign t in
    log 5 " -> %a" Expr.debug_term res;
    res
  with Expr.Cannot_assign _ ->
    _fail (Util.sprintf
             "Expected to be able to assign symbol %a\nYou may have forgotten to activate an extension" Expr.debug_term t)

let rec iter_assign_aux f e = match Expr.(e.term) with
  | Expr.App (p, _, l) ->
    if not (Expr.is_interpreted p) then f e;
    List.iter (iter_assign_aux f) l
  | _ -> f e

let iter_assignable f e =
  preprocess e;
  match Expr.(e.formula) with
  | Expr.Equal (a, b) -> iter_assign_aux f a; iter_assign_aux f b
  | Expr.Pred p -> iter_assign_aux f p
  | _ -> ()

exception Found_eval of bool * int
let eval_aux f =
  try
    ext_iter (fun ext ->
        match ext.eval_pred f with
        | Some (b, lvl) -> raise (Found_eval (b, lvl))
        | _ -> ());
    Unknown
  with Found_eval (b, lvl) ->
    Valued (b, lvl)

let eval formula =
  log 5 "Evaluating formula : %a" Expr.debug_formula formula;
  match formula with
  | { Expr.formula = Expr.Not f } -> begin match eval_aux f with
      | Valued (b, lvl) -> Valued (not b, lvl)
      | Unknown -> Unknown
    end
  | f -> eval_aux f


