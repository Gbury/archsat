
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

(* TODO: translate symbol (and type) to proof term,
         and treat implicit declarations *)

let declare_ty opt v =
  if Options.(opt.context) then begin
    (* pp_opt Coq.declare_ty Options.(opt.proof.coq) v *)
    ()
  end

let declare_term opt v =
  if Options.(opt.context) then begin
    (* pp_opt Coq.declare_term Options.(opt.proof.coq) v *)
    ()
  end

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



