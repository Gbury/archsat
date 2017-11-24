
let section = Section.make "proving"

(* Small wrapper *)
(* ************************************************************************ *)

(* Printing on optional formatters *)
let pp_opt pp o x =
  match o with
  | None -> ()
  | Some fmt -> pp fmt x

(* Proof hyps *)
(* ************************************************************************ *)

module H = Hashtbl.Make(Dolmen.Id)

(* mutable state *)
let goals = ref []

let add_goal id g =
  begin match !goals with
    | [] -> ()
    | _ -> Util.warn ~section "%s%s"
             "Multiple goals are not very well supported,@ "
             "please consider having a single goal at any time"
  end;
  goals := (id, g) :: !goals

let get_goals () = !goals

let clear_goals () = goals := []

(* Proof context *)
(* ************************************************************************ *)

(* Wrapper to get implicitly typed identifiers. *)
let wrapper t tr =
  let l = ref [] in
  let callback = Some (function id -> l := id :: !l) in
  let res = tr ?callback t in
  !l, res

let print_id_typed fmt id =
  Format.fprintf fmt "%a: @[<hov>%a@]"
    Expr.Print.id id Term.print id.Expr.id_type

(* Print type declarations for ids *)
let declare_id opt implicit v ty =
  let id = Expr.Id.mk_new v.Expr.id_name ty in
  let () = Term.trap_id v id in
  if Options.(opt.context) then begin
    List.iter (fun x ->
        pp_opt Coq.declare_id Options.(opt.coq) x;
        ()
      ) (List.rev (id :: implicit))
  end else begin match implicit with
    | [] -> ()
    | _ ->
      Util.warn ~section
        "@[<hv 2>The following identifiers are implicitly typed:@ @[<v>%a@]@]"
        CCFormat.(list ~sep:(return "@ ") print_id_typed) implicit
  end

(* Declare type consructors *)
let declare_ty opt v =
  Util.debug ~section "Translating %a" Expr.Print.id v;
  let implicit, ty = wrapper v.Expr.id_type
      (Term.of_function_descr Term.of_unit Term.of_ttype)
  in
  declare_id opt implicit v ty

(* Declare term constants *)
let declare_term opt v =
  Util.debug ~section "Translating %a" Expr.Print.id v;
  let implicit, ty = wrapper v.Expr.id_type
      (Term.of_function_descr Term.of_ttype Term.of_ty)
  in
  declare_id opt implicit v ty

let declare_hyp opt id =
  if Options.(opt.context) then begin
    ()
  end

let declare_goal opt id f =
  if Options.(opt.context) then begin
    ()
  end

(* Proving lemmas *)
(* ************************************************************************ *)

type _ Dispatcher.msg +=
  | Lemma : Dispatcher.lemma_info -> Proof.proof Dispatcher.msg


(* Output proofs *)
(* ************************************************************************ *)

let output_proof opt p =
  let () = pp_opt Unsat_core.print Options.(opt.unsat_core) p in
  let () = pp_opt Dot.print Options.(opt.dot) p in
  ()



