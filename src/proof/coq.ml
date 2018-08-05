
let section = Section.make "coq"

let formula a = a.Dispatcher.SolverTypes.lit

(* Printing wrappers *)
(* ************************************************************************ *)

module Print = struct

  let pos = Tag.create ()
  let name = Tag.create ()
  let assoc = Tag.create ()
  type any = Any : Term.id * 'a Expr.tag * 'a -> any

  let () =
    List.iter (function Any (id, tag, v) -> Expr.Id.tag id tag v) [
      Any (Term.equal_id, name,   Pretty.Exact "=");
      Any (Term.equal_id, pos,    Pretty.Infix);
      Any (Term._Prop_id, name,   Pretty.Exact "Prop");
      Any (Term.true_id,  name,   Pretty.Exact "True");
      Any (Term.false_id, name,   Pretty.Exact "False");
      Any (Term.not_id,   name,   Pretty.Exact "~");
      Any (Term.not_id,   pos,    Pretty.Prefix);
      Any (Term.imply_id, name,   Pretty.Exact "->");
      Any (Term.imply_id, pos,    Pretty.Infix);
      Any (Term.equiv_id, name,   Pretty.Exact "<->");
      Any (Term.equiv_id, pos,    Pretty.Infix);
      Any (Term.or_id,    name,   Pretty.Exact {|\/|});
      Any (Term.or_id,    pos,    Pretty.Infix);
      Any (Term.or_id,    assoc,  Pretty.Right);
      Any (Term.and_id,   name,   Pretty.Exact {|/\|});
      Any (Term.and_id,   pos,    Pretty.Infix);
      Any (Term.and_id,   assoc,  Pretty.Right);
    ]

  let t =
    let name = Escape.tagged_name ~tags:[name; Term.disambiguate_tag] in
    let rename = Escape.rename ~sep:'_' in
    let escape = Escape.umap (fun i -> function
        | None -> [ Uchar.of_char '_' ]
        | Some c ->
          let g = Uucp.Gc.general_category c in
          begin match g with
            | `Lu | `Ll | `Lt | `Lm | `Lo | `Sm -> [ c ]
            | `Nd when i > 1 -> [ c ]
            | _ -> [ Uchar.of_char '_' ]
          end) in
    Escape.mk ~lang:"coq" ~name ~escape ~rename

  let id fmt v = Escape.id t fmt v

  let get_status = function
    | { Term.term = Term.Id f } ->
      Expr.Id.get_tag f pos
    | _ -> None

  let binder_name = function
    | Term.Forall -> "forall"
    | Term.Exists -> "exists"
    | Term.Lambda -> "fun"

  let binder_sep = function
    | Term.Lambda -> " =>"
    | Term.Forall
    | Term.Exists -> ","

  let rec elim_implicits t args =
    match t.Term.term, args with
    | _, [] -> []
    | Term.Binder (Term.Forall, v, body), (hd :: tl) ->
      if Term.is_coq_implicit v then elim_implicits body tl
      else if Term.is_coq_inferred v then None :: elim_implicits body tl
      else Some hd :: elim_implicits body tl
    | _ -> List.map CCOpt.return args

  let rec term_aux ~fragile fmt t =
    let t = if fragile then t else Term.contract t in
    match t.Term.term with
    | Term.Type -> Format.fprintf fmt "Type"
    | Term.Id v -> id fmt v
    | Term.App _ ->
      let f, args = Term.uncurry ~assoc t in
      let args = elim_implicits Term.(reduce @@ ty f) args in
      begin match get_status f, args with
        | None, [] ->
          Format.fprintf fmt "@[<hov>%a@]" (term_aux ~fragile:false) f
        | None, _ ->
          Format.fprintf fmt "@[<hov>(%a %a)@]" (term_aux ~fragile:false) f
            CCFormat.(list ~sep:(return "@ ") term_arg) args
        | Some Pretty.Prefix, _ ->
          Format.fprintf fmt "@[<hov>%a %a@]" (term_aux ~fragile:false) f
            CCFormat.(list ~sep:(return "@ ") term_arg) args
        | Some Pretty.Infix, _ ->
          let sep fmt () = Format.fprintf fmt "@ %a " (term_aux ~fragile:false) f in
          Format.fprintf fmt "@[<hov>(%a)@]" CCFormat.(list ~sep term_arg) args
      end
    | Term.Let (v, e, body) ->
      Format.fprintf fmt "@[<v>@[<hv>let %a := @[<hov>%a@]@ in@]@ %a@]"
        id v (term_aux ~fragile:false) e (term_aux ~fragile:false) body
    | Term.Binder (b, _, _) ->
      let kind, vars, body = Term.flatten_binder t in
      begin match kind with
        | `Arrow ->
          let tys = List.map (fun id -> id.Expr.id_type) vars in
          Format.fprintf fmt "(@[<hov>%a ->@ %a@])"
            CCFormat.(list ~sep:(return "@ -> ") (term_aux ~fragile:false)) tys
            (term_aux ~fragile:false) body
        | `Pi | `Binder _ ->
          let l = Term.concat_vars vars in
          Format.fprintf fmt "(@[<hov 2>%s @[<hov>%a@]%s@ %a@])"
            (binder_name b) var_lists l
            (binder_sep b) (term_aux ~fragile:false) body
      end

  and term_arg fmt = function
    | None -> Format.fprintf fmt "_"
    | Some t -> term_aux ~fragile:false fmt t

  and var_list fmt (ty, l) =
    assert (l <> []);
    Format.fprintf fmt "(%a:@ %a)"
      CCFormat.(list ~sep:(return "@ ") id) l
      (term_aux ~fragile:false) ty

  and var_lists fmt l =
    CCFormat.(list ~sep:(return "@ ") var_list) fmt l

  let term = CCFormat.hovbox (term_aux ~fragile:false)

  let fragile = CCFormat.hovbox (term_aux ~fragile:true)

end

(* Printing contexts *)
(* ************************************************************************ *)

let init fmt opt =
  Format.fprintf fmt
    "@\n(**@[<v>@ %s@ Input file: %s@]@ **)@]@\n@."
    "Proof automatically generated by Archsat"
    Options.(input_to_string opt.input.file)

let declare_loc fmt = function
  | None ->
    Format.fprintf fmt "(* Implicitly declared *)"
  | Some l ->
    Format.fprintf fmt "(* @[<hov>%a@] *)" Dolmen.ParseLocation.fmt l

let declare_id ?loc fmt id =
  Format.fprintf fmt "%a@\nParameter %a : %a.@\n@."
    declare_loc loc Print.id id Print.term id.Expr.id_type

let declare_hyp ?loc fmt id =
  Format.fprintf fmt "%a@\nAxiom %a : %a.@\n@."
    declare_loc loc Print.id id Print.term id.Expr.id_type

let declare_goal ?loc fmt id =
  Format.fprintf fmt "%a@\nTheorem %a : %a.@."
    declare_loc loc Print.id id Print.term id.Expr.id_type

let declare_goal_term ?loc fmt id =
  Format.fprintf fmt "%a@\n@[<v 2>@[<hv 2>Definition@ %a :@ %a@ :=@]@\n"
    declare_loc loc Print.id id Print.term id.Expr.id_type

let proof_context pp fmt x =
  Format.fprintf fmt "@[<hov 2>Proof.@\n%a@]@\nQed.@." pp x

let proof_term_context pp fmt x =
  Format.fprintf fmt "%a@].@." pp x

