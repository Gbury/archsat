
let section = Section.make "proof"

(* Proof environments *)
(* ************************************************************************ *)

module Env = struct

  exception Added_twice of Term.t
  exception Not_introduced of Term.t

  let () =
    Printexc.register_printer (function
        | Added_twice f ->
          Some (Format.asprintf
                  "Following formula has been added twice to context:@ %a"
                  Term.print f)
        | Not_introduced f ->
          Some (Format.asprintf
                  "Following formula is used in a context where it is not declared:@ %a"
                  Term.print f)
        | _ -> None
      )

  module Mt = Map.Make(Term)
  module Ms = Map.Make(String)

  type t = {
    (** Map between terms and term ids *)
    names : Term.id Mt.t;
    (** Options for nive names *)
    prefix : string;  (** current prefix *)
    count : int Ms.t; (** use count for each prefix *)
  }

  let empty = {
    names = Mt.empty;
    prefix = "";
    count = Ms.empty;
  }

  let prefix t s =
    { t with prefix = s }

  let mem t f =
    Mt.mem f t.names

  let find t f =
    try Mt.find f t.names
    with Not_found -> raise (Not_introduced f)

  let count t s =
    try Ms.find s t.count with Not_found -> 0

  let intro t f =
    match Mt.find f t.names with
    | name -> raise (Added_twice f)
    | exception Not_found ->
      let n = count t t.prefix in
      let name = Format.sprintf "%s%d" t.prefix n in
      let id = Expr.Id.mk_new name f in
      { t with
        names = Mt.add f id t.names;
        count = Ms.add t.prefix (n + 1) t.count;
      }

  let print_aux fmt (t, id) =
    Format.fprintf fmt "%a: @[<hov>%a@]" Expr.Print.id id Term.print t

  let print fmt t =
    let l = Mt.bindings t.names in
    let l = List.sort (fun (_, x) (_, y) ->
        compare x.Expr.id_name y.Expr.id_name) l in
    CCFormat.(list ~sep:(return "@ ") print_aux) fmt l

end

(* Proof printing data *)
(* ************************************************************************ *)

type lang =
  | Coq     (**)
(* Proof languages supported. *)

type pretty =
  | Branching           (* All branches are equivalent *)
  | Last_but_not_least  (* Last branch is the 'rest of the proof *)
(** Pretty pinting information to know better how to print proofs.
    For instance, 'split's would probably be [Branching], while
    cut/pose proof, would preferably be [Last_but_not_least]. *)

(* Proofs *)
(* ************************************************************************ *)

type ctx = {
  env : Env.t;
  goal : Term.t;
}

type 'state step = {

  (* Printing information *)
  print : lang ->
    pretty * (Format.formatter -> 'state -> unit);

  (* Semantics *)
  compute : ctx -> 'state * ctx array;
  elaborate : 'state -> Term.t array -> Term.t;
}

type proof_step =
  | Any : 'a * 'a step -> proof_step

type t = opt array

and opt =
  | Open of ctx
  | Proof of node

and node = {
  step : proof_step;
  branches : t;
}

(* Some aliases *)

type proof = t

type pos = t * int

(* Contexts *)
(* ************************************************************************ *)

let env { env; _ } = env
let goal { goal; _ } = goal
let mk_ctx env goal = Env.{ env; goal; }

let print_ctx fmt ctx =
  Format.fprintf fmt
    "@[<hv 2>ctx:@ @[<hv 2>env:@ @[<v>%a@]@] @[<hv 2>goal:@ @[<hov>%a@]@]@]"
    Env.print ctx.env Term.print ctx.goal

(* Failure *)
(* ************************************************************************ *)

exception Failure of string * ctx

let () = Printexc.register_printer (function
    | Failure (msg, ctx) ->
      Some (Format.asprintf "@[<hv>In context:@ %a@ %s@]" print_ctx ctx msg)
    | _ -> None)

(* Steps *)
(* ************************************************************************ *)

let mk_step ~coq ~compute ~elaborate = {
  print = (function Coq -> coq);
  compute; elaborate;
}

(* Building proofs *)
(* ************************************************************************ *)

let mk env goal =
  let res = [| Open { env; goal; } |] in
  res, (res, 0)

let get_pos (t, i) = t.(i)

let apply_step (t, i) step =
  match get_pos (t, i) with
  | Proof _ ->
    Util.error ~section "Trying to apply reasonning step to an aleardy closed proof";
    assert false
  | Open ctx ->
    let y, a = step.compute ctx in
    let branches = Array.map (fun ctx -> Open ctx) a in
    let res = { step = Any (y, step); branches } in
    let () = t.(i) <- Proof res in
    y, Array.init (Array.length a) (fun i -> (branches, i))


(* Printing proofs *)
(* ************************************************************************ *)

exception Open_proof

let bullet_list = [ '-'; '+' ]
let bullet_n = List.length bullet_list

let bullet depth =
  let k = depth mod bullet_n in
  let n = depth / bullet_n + 1 in
  let c = List.nth bullet_list k in
  String.make n c

let rec print_branching_coq ~depth fmt t =
  Format.fprintf fmt "%s @[<hov>%a@]"
    (bullet depth) (print_opt ~depth:(depth + 1) ~lang:Coq) t

and print_bracketed_coq ~depth fmt t =
  Format.fprintf fmt "{ @[<hov>%a@] }" (print_opt ~depth ~lang:Coq) t

and print_lbnl_coq ~depth fmt t =
  print_opt ~depth ~lang:Coq fmt t

and print_array_coq ~depth ~pretty fmt a =
  match a with
  | [| |] -> ()
  | [| x |] -> print_opt ~depth ~lang:Coq fmt x
  | _ ->
    begin match pretty with
      | Branching ->
        Format.fprintf fmt "@[<v>%a@]"
          CCFormat.(array ~sep:(return "@ ") (print_branching_coq ~depth)) a
      | Last_but_not_least ->
        let a' = Array.sub a 0 (Array.length a - 1) in
        Format.fprintf fmt "@[<v>%a@ @]"
          CCFormat.(array ~sep:(return "@ ") (print_bracketed_coq ~depth)) a';
        print_lbnl_coq ~depth fmt a.(Array.length a - 1)
    end

and print_array ~depth ~lang ~pretty fmt a =
  match lang with
  | Coq -> print_array_coq ~depth ~pretty fmt a

and print_opt ~depth ~lang fmt = function
  | Proof t -> print_node ~depth ~lang fmt t
  | Open _ -> raise Open_proof

and print_node ~depth ~lang fmt { step = Any (state, step); branches; } =
  let pretty, pp = step.print lang in
  Format.fprintf fmt "@[<hov 2>%a@]" pp state;
  print_array ~depth ~lang ~pretty fmt branches

let print_proof ~lang fmt = function
  | [| p |] -> print_opt ~lang ~depth:0 fmt p
  | _ -> assert false


(* Proof elaboration *)
(* ************************************************************************ *)

let rec elaborate_array_aux k a res i =
  if i >= Array.length a then k res
  else
    elaborate_opt (fun x ->
        res.(i) <- x;
        elaborate_array_aux k a res (i + 1)) a.(i)

and elaborate_array k a =
  let res = Array.make (Array.length a) Term._Type in
  elaborate_array_aux k a res 0

and elaborate_node k { step = Any (state, step); branches; } =
  elaborate_array (fun args -> k @@ step.elaborate state args) branches

and elaborate_opt k = function
  | Proof t -> elaborate_node k t
  | Open _ -> raise Open_proof

let elaborate = function
  | [| p |] -> elaborate_opt (fun x -> x) p
  | _ -> assert false


