
(* Type definitions *)
(* ************************************************************************ *)

module M = Map.Make(Expr.Term)

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

type level = {
  eval_map : (term * int) M.t;
  wait_eval : term list M.t;
  watch_map : ((term * term) -> unit) list M.t;
  ext_levels : int Vec.t;
}

type res =
  | Sat of level
  | Unsat of formula list * proof

type eval_res =
  | Valued of bool * int
  | Unknown

(* Extensions registering *)
(* ************************************************************************ *)

exception Absurd of formula list
exception Extension_not_found of string

type extension = {
  name : string;
  assume : slice -> unit;
  assign : term -> term option;
  eval : term -> (bool * int) option;
  interprets : Expr.ty Expr.function_descr Expr.var -> bool;
  backtrack : int -> unit;
  current_level : unit -> int;
}

let dummy_ext = {
  name = "";
  assume = (fun _ -> assert false);
  assign = (fun _ -> assert false);
  eval = (fun _ -> assert false);
  interprets = (fun _ -> assert false);
  backtrack = (fun _ -> assert false);
  current_level = (fun _ -> assert false);
}

let extensions = ref []

let active = Vec.make 10 dummy_ext

let register r = extensions := r :: !extensions

let activate ext =
  let aux r = r.name = ext in
  try
    let r = List.find aux !extensions in
    assert (not (Vec.exists aux active));
    Vec.push active r
  with Not_found ->
    raise (Extension_not_found ext)

let n_ext () = Vec.size active

let ext_get i = Vec.get active i

let is_interpreted f = Vec.exists (fun r -> r.interprets f) active

(* Evaluation/Watching functions *)
(* ************************************************************************ *)

(* The current assignment map, term -> value *)
let eval_map = ref M.empty
(* Map of terms watching other terms, term -> list of terms to evaluate when arg has value *)
let wait_eval = ref M.empty
(* Map of terms watched by extensions, term -> continuation list *)
let watch_map = ref M.empty

let is_assigned t = try ignore(M.find t !eval_map); true with Not_found -> false

let get_assign t = M.find t !eval_map

let add_wait_eval t t' =
    let l = try M.find t' !wait_eval with Not_found -> [] in
    wait_eval := M.add t' (t :: l) !wait_eval

let try_eval t =
    assert (not (is_assigned t));
    match Expr.(t.term) with
    | Expr.App (f, _, l) when is_interpreted f -> () (* TODO *)
    | Expr.App (f, _, l) -> () (* Can't do anything but wait for it to be assigned *)
    | _ -> ()

let set_assign t v lvl =
    eval_map := M.add t (v, lvl) !eval_map

(* Mcsat Plugin functions *)
(* ************************************************************************ *)

let dummy = {
  eval_map = M.empty;
  wait_eval = M.empty;
  watch_map = M.empty;
  ext_levels = Vec.make_empty ~-1;
}

let current_level () = {
  eval_map = !eval_map;
  wait_eval = !wait_eval;
  watch_map = !watch_map;
  ext_levels = Vec.init (Vec.size active)
      (fun i -> (ext_get i).current_level ()) ~-1;
}

let backtrack s =
  eval_map := s.eval_map;
  wait_eval := s.wait_eval;
  watch_map := s.watch_map

let assume s =
    for i = s.start to s.start + s.length - 1 do
        match s.get i with
        | Lit _, _ -> ()
        | Assign (t, v), lvl -> set_assign t v lvl
    done;
    let i = ref 0 in
    try
        while !i < Vec.size active do
            (ext_get !i).assume s
        done;
        Sat (current_level ())
    with Absurd l ->
        Unsat (l, !i)

let assign t =
    let res = ref None in
    begin try
        for i = 0 to n_ext () - 1 do
            match (ext_get i).assign t with
            | None -> ()
            | Some v -> res := Some v; raise Exit
        done;
    with Exit ->
        ()
    end;
    match !res with
    | None -> assert false
    | Some v -> v

let rec iter_assign_aux f e = match Expr.(e.term) with
    | Expr.App (p, _, l) ->
            if not (is_interpreted p) then f e;
            List.iter (iter_assign_aux f) l
    | _ -> f e

let iter_assignable f e = match Expr.(e.formula) with
    | Expr.Equal (a, b) -> iter_assign_aux f a; iter_assign_aux f b
    | Expr.Pred p -> iter_assign_aux f p
    | _ -> ()

let rec eval f = match Expr.(f.formula) with
    | Expr.Equal (a, b) ->
            begin try
                let a', lvl_a = get_assign a in
                let b', lvl_b = get_assign b in
                Valued (Expr.Term.equal a' b', max lvl_a lvl_b)
            with Not_found ->
                Unknown
            end
    | Expr.Pred p ->
            let res = ref Unknown in
            begin try
                for i = 0 to n_ext () - 1 do
                    match (ext_get i).eval p with
                    | None -> ()
                    | Some (b, lvl) -> res := Valued (b, lvl); raise Exit
                done;
                raise Exit
            with Exit ->
                !res
            end
    | Expr.Not f' -> begin match eval f' with
        | Valued (b, lvl) -> Valued (not b, lvl)
        | Unknown -> Unknown
    end
    | _ -> Unknown



