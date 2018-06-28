
let section = Section.make "export"

(* Some convenience functions *)
(* ************************************************************************ *)

(* Printing on optional formatters *)
let pp_opt pp o x =
  match o with
  | None -> ()
  | Some fmt -> pp fmt x

(* Initialization *)
(* ************************************************************************ *)

let init opts () =
  let () = pp_opt Tptp.init Options.(opts.output.tptp) opts in
  ()

(* Id declarations *)
(* ************************************************************************ *)

let declare_id_aux ?loc opt (name, id) =
  let () = pp_opt (Tptp.declare_id ?loc) Options.(opt.output.tptp) (name, id) in
  ()

let _implicit = ref 0

let declare_implicits opt = function
  | [] -> ()
  | l -> List.iter (fun id ->
      let () = incr _implicit in
      let name = Dolmen.Id.(mk decl) @@
        Format.asprintf "implicit_%d" !_implicit
      in
      declare_id_aux opt (name, id)
    ) l

(* Top-level wrappers *)
(* ************************************************************************ *)

let declare_id ?loc opt implicit (name, id) =
  let () = declare_implicits opt implicit in
  let () = declare_id_aux ?loc opt (name, id) in
  ()

let declare_hyp ?loc opt implicit t =
  let () = declare_implicits opt implicit in
  let () = pp_opt (Tptp.declare_hyp ?loc) Options.(opt.output.tptp) t in
  ()

let declare_goal ?loc opt implicit t =
  let () = declare_implicits opt implicit in
  let () = pp_opt (Tptp.declare_goal ?loc) Options.(opt.output.tptp) t in
  ()

let declare_solve ?loc opt () =
  let () =pp_opt (Tptp.declare_solve ?loc) Options.(opt.output.tptp) () in
  ()

