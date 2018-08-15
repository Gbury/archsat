
let section = Section.make "tptp"

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
      Any (Term._Prop_id, name,   Pretty.Exact "$o");
      Any (Term.true_id,  name,   Pretty.Exact "$true");
      Any (Term.false_id, name,   Pretty.Exact "$false");
      Any (Term.not_id,   name,   Pretty.Exact "~");
      Any (Term.not_id,   pos,    Pretty.Prefix);
      Any (Term.imply_id, name,   Pretty.Exact "=>");
      Any (Term.imply_id, pos,    Pretty.Infix);
      Any (Term.equiv_id, name,   Pretty.Exact "<=>");
      Any (Term.equiv_id, pos,    Pretty.Infix);
      Any (Term.or_id,    name,   Pretty.Exact "|");
      Any (Term.or_id,    pos,    Pretty.Infix);
      Any (Term.or_id,    assoc,  Pretty.Left);
      Any (Term.and_id,   name,   Pretty.Exact "&");
      Any (Term.and_id,   pos,    Pretty.Infix);
      Any (Term.and_id,   assoc,  Pretty.Left);
    ]

  let is_dollar c = Uchar.equal c (Uchar.of_char '$')
  let is_underscore c = Uchar.equal c (Uchar.of_char '_')

  let is_alpha c = Uucp.Alpha.is_alphabetic c
  let is_num c = Uucp.Num.numeric_type c <> `None

  (** Alphanumeric characters as defined by tptp (yes, it includes underscores, :p ) *)
  let is_alphanum c = is_alpha c || is_num c || is_underscore c

  let var_escape =
    let name = Escape.tagged_name ~tags:[name] in
    let rename = Escape.rename ~sep:'_' in
    let escape = Escape.umap (fun i -> function
        | None -> [ Uchar.of_char '_' ]
        | Some c ->
          begin match Uucp.Block.block c with
            | `ASCII when i = 1 && is_underscore c ->
              [Uchar.of_char 'V'; c]
            | `ASCII when i = 1 && Uucp.Case.is_lower c ->
              begin match Uucp.Case.Map.to_upper c with
                | `Self -> [ c ]
                | `Uchars l -> l @ [Uchar.of_char '_']
              end
            | `ASCII when (i = 1 && is_dollar c) || is_alphanum c ->
              [ c ]
            | _ -> [ Uchar.of_char 'V'; Uchar.of_char '_' ]
          end) in
    Escape.mk ~lang:"tptp" ~name ~escape ~rename

  let cst_escape =
    let name = Escape.tagged_name ~tags:[name] in
    let rename = Escape.rename ~sep:'_' in
    let escape = Escape.umap (fun i -> function
        | None -> [ Uchar.of_char '_' ]
        | Some c ->
          begin match Uucp.Block.block c with
            | `ASCII when i = 1 && is_underscore c ->
              [Uchar.of_char 'V'; c]
            | `ASCII when i = 1 && Uucp.Case.is_upper c ->
              begin match Uucp.Case.Map.to_lower c with
                | `Self -> [ c ]
                | `Uchars l -> l @ [Uchar.of_char '_']
              end
            | `ASCII when (i = 1 && is_dollar c) || is_alphanum c ->
              [ c ]
            | _ -> [ Uchar.of_char '_' ]
          end) in
    Escape.mk ~lang:"tptp" ~name ~escape ~rename

  let var fmt v = Escape.id var_escape fmt v
  let cst fmt v = Escape.id cst_escape fmt v
  let dolmen fmt v = Escape.dolmen cst_escape fmt v

  let get_status = function
    | { Term.term = Term.Id f } ->
      Expr.Id.get_tag f pos
    | _ -> None

  let binder_name = function
    | Term.Forall -> "!"
    | Term.Exists -> "?"
    | Term.Lambda -> "^"

  let binder_sep = function
    | Term.Lambda
    | Term.Forall
    | Term.Exists -> " :"

  let rec elim_implicits t args =
    match t.Term.term with
    | Term.Binder (Term.Forall, v, body) when Term.is_tptp_implicit v ->
      elim_implicits body (List.tl args)
    | _ -> args

  let rec term fmt t =
    match t.Term.term with
    | Term.Type -> Format.fprintf fmt "$tType"
    | Term.Id v -> if Term.is_var v then var fmt v else cst fmt v
    | Term.App _ ->
      let f, args = Term.uncurry ~assoc t in
      let args = elim_implicits f.Term.ty args in
      begin match get_status f, args with
        | None, [] ->
          Format.fprintf fmt "@[<hov>%a@]" term f
        | None, _ ->
          Format.fprintf fmt "@[<hov>%a(%a)@]" term f
            CCFormat.(list ~sep:(return ",@ ") term) args
        | Some Pretty.Prefix, _ ->
          Format.fprintf fmt "@[<hov>(%a@ %a)@]" term f
            CCFormat.(list ~sep:(return "@ ") term) args
        | Some Pretty.Infix, _ ->
          let sep fmt () = Format.fprintf fmt "@ %a " term f in
          Format.fprintf fmt "@[<hov>(%a)@]" CCFormat.(list ~sep term) args
      end
    | Term.Let (v, e, body) ->
      Format.fprintf fmt "@[<v>@[<hv>$let(%a :@ %a, %a :=@ @[<hov>%a@],@]@ %a)@]"
        cst v term v.Expr.id_type
        cst v term e term body
    | Term.Binder _ ->
      let kind, vars, body = Term.flatten_binder t in
      begin match kind with
        | `Arrow ->
          let tys = List.map (fun id -> id.Expr.id_type) vars in
          Format.fprintf fmt "@[<hov>%a >@ %a@]" product_type tys term body
        | `Pi ->
          Format.fprintf fmt "(@[<hov 2>!> @[<hov>[%a]@]%s@ ( %a ) @])"
            var_list vars (binder_sep Term.Forall) term body
        | `Binder b ->
          Format.fprintf fmt "(@[<hov 2>%s @[<hov>[%a]@]%s@ %a@])"
            (binder_name b) var_list vars (binder_sep b) term body
      end

  and product_type fmt = function
    | [] -> assert false
    | [ t ] -> term fmt t
    | l ->
      Format.fprintf fmt "( %a )"
        CCFormat.(list ~sep:(return "@ * ") term) l

  and var_typed fmt v =
    Format.fprintf fmt "%a:@ %a" var v term v.Expr.id_type

  and var_list fmt l =
    CCFormat.(list ~sep:(return "@ , ") var_typed) fmt l

end

(* Detect higher order *)
(* ************************************************************************ *)

let rec ho_id v = ho_term v.Expr.id_type

and ho_term t =
  match t.Term.term with
  | Term.Type -> false
  | Term.Id v -> ho_id v
  | Term.App (f, arg) -> ho_term f || ho_term arg
  | Term.Let (v, e, body) -> ho_id v || ho_term e || ho_term body
  | Term.Binder (Term.Lambda, _, _) -> true
  | Term.Binder (_, v, body) -> ho_id v || ho_term body

(* Printing contexts *)
(* ************************************************************************ *)

let init fmt opt =
  Format.fprintf fmt
    "@\n/*@[<v>@ %s@ Input file: %s@]@ */@]@\n@."
    "Translation automatically generated by Archsat"
    Options.(input_to_string opt.input.file)

let declare_loc fmt = function
  | None ->
    Format.fprintf fmt "%%-- Implicitly declared"
  | Some l ->
    Format.fprintf fmt "%%-- @[<h>%a@]" Dolmen.ParseLocation.fmt l

let kind b = if b then "thf" else "tff"

let declare_id ?loc fmt (name, id) =
  (* Do not declare $i *)
  if Term.equal (Term.id id) (Term.of_ty Expr.Ty.base) then ()
  (* Regular declarations *)
  else begin
    Format.fprintf fmt "%a@\n%s(@[<hv>%a, type, (@ @[<hov>%a : %a ) )@]@].@\n@."
      declare_loc loc (kind @@ ho_id id)
      Print.dolmen name
      Print.cst id Print.term id.Expr.id_type
  end

let declare_hyp ?loc fmt id =
  Format.fprintf fmt "%a@\n%s(@[<hv>%a, axiom,@ @[<hov>%a)@]@].@\n@."
    declare_loc loc (kind @@ ho_id id)
    Print.cst id Print.term id.Expr.id_type

let goal_declared = ref false

let declare_goal ?loc fmt id =
  if !goal_declared then
    Util.error ~section "Multiple goals are not supported in tptp files."
  else begin
    let () = goal_declared := true in
    Format.fprintf fmt "%a@\n%s(@[<hv>%a, conjecture,@ @[<hov>%a)@]@].@\n@."
      declare_loc loc (kind @@ ho_id id)
      Print.cst id Print.term id.Expr.id_type
  end

let declare_solve ?loc fmt () =
  if !goal_declared then ()
  else declare_goal ?loc fmt (Term.declare "implicit_goal" Term.false_term)

