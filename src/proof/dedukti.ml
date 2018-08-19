(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

let section = Section.make "dedukti"

let formula a = a.Dispatcher.SolverTypes.lit

(* Printing wrappers *)
(* ************************************************************************ *)

module Print = struct

  let pos = Tag.create ()
  let name = Tag.create ()
  let assoc = Tag.create ()
  let variant = Tag.create ()
  type any = Any : Term.id * 'a Expr.tag * 'a -> any

  let () =
    List.iter (function Any (id, tag, v) -> Expr.Id.tag id tag v) [
      Any (Term.equal_id, name,   Pretty.Exact "logic.equal");
      Any (Term._Prop_id, name,   Pretty.Exact "logic.prop");
      Any (Term.true_id,  name,   Pretty.Exact "logic.True");
      Any (Term.false_id, name,   Pretty.Exact "logic.False");
      Any (Term.not_id,   name,   Pretty.Exact "logic.not");
      Any (Term.imply_id, name,   Pretty.Exact "logic.imp");
      Any (Term.equiv_id, name,   Pretty.Exact "logic.equiv");
      Any (Term.or_id,    name,   Pretty.Exact "logic.or");
      Any (Term.and_id,   name,   Pretty.Exact "logic.and");
    ]

  let is_alpha c = Uucp.Alpha.is_alphabetic c
  let is_num c = Uucp.Num.numeric_type c <> `None
  let is_alphanum c = is_alpha c || is_num c

  (* TODO: change this code as soone as official syntax description is available. *)
  let t =
    let name = Escape.tagged_name ~tags:[name; Term.disambiguate_tag] in
    let rename = Escape.rename ~sep:'_' in
    let escape = Escape.umap (fun i -> function
        | None -> [ Uchar.of_char '_' ]
        | Some c ->
          begin match Uucp.Block.block c with
            | `ASCII when (i = 1 && is_alpha c) || is_alphanum c -> [c]
            | _ -> [ Uchar.of_char '_' ]
          end
      ) in
    Escape.mk ~lang:"dedukti" ~name ~escape ~rename

  let id fmt v = Escape.id t fmt v

  let is_arrow t =
    match t.Term.term with
    | Term.Binder _ ->
      begin match Term.flatten_binder t with
        | (`Arrow | `Pi), _, _ ->
          not @@ Term.Reduced.equal Term._Prop (Term.ty t)
        | _ -> false
      end
    | _ -> false

  let get_variant t args =
    match t with
    | { Term.term = Term.Id f } ->
      begin match Expr.Id.get_tag f variant with
        | Some v -> v args
        | None -> t, args
      end
    | _ -> t, args

  let get_status = function
    | { Term.term = Term.Id f } ->
      Expr.Id.get_tag f pos
    | _ -> None

  let rec term_aux ~simplify ~fragile fmt t =
    let t = if simplify then Term.contract t else t in
    match t.Term.term with
    | Term.Type -> Format.fprintf fmt "logic.type"
    | Term.Id v -> id fmt v

    (* Application *)
    | Term.App _ ->
      let f, args = Term.uncurry ~assoc t in
      pp_app ~fragile fmt f args

    (* Let-binding *)
    | Term.Let (v, e, body) ->
      Format.fprintf fmt "%s(%a =>@ %a@;) %a%s"
        (if fragile then "(" else "")
        var_type v
        (term_aux ~fragile:false ~simplify:true) body
        (term_aux ~fragile:true ~simplify:true) e
        (if fragile then ")" else "")

    (* Other binders *)
    | Term.Binder (b, v, t') ->
      let kind, vars, body = Term.flatten_binder t in
      begin match kind with
        | `Arrow when Term.Reduced.equal Term._Prop (Term.ty t) ->
          pp_app ~fragile fmt Term.imply_term ([v.Expr.id_type; t'])
        | `Arrow ->
          let tys = List.map (fun id -> id.Expr.id_type) vars in
          Format.fprintf fmt "(@[<hov>%a ->@ %a@])"
            CCFormat.(list ~sep:(return "@ -> ") (type_aux ~simplify:true)) tys
            (type_aux ~simplify:true) body
        | `Pi when Term.Reduced.equal Term._Prop (Term.ty t) ->
          quant ~fragile fmt "logic.forall" v t'
        | `Binder Term.Forall -> quant ~fragile fmt "logic.forall" v t'
        | `Binder Term.Exists -> quant ~fragile fmt "logic.exists" v t'
        | `Pi | `Binder Term.Lambda ->
          let sep, pp_arg = match kind with
            | `Pi -> "->", type_aux
            | _ -> "=>", term_aux ~fragile:false
          in
          Format.fprintf fmt "@[<hov>%s%a %s@ %a%s@]"
            (if fragile then "(" else "")
            (var_list sep) vars sep
            (pp_arg ~simplify:true) body
            (if fragile then ")" else "")
      end

  and type_aux ~simplify fmt ty =
    let wrapper, fragile =
      if Term.Reduced.equal Term._Prop (Term.ty ty) then "logic.proof ", true
      else if Term.Reduced.equal Term._Prop ty ||
              Term.Reduced.equal Term._Type ty || is_arrow ty then "", false
      else "logic.term ", true
    in
    Format.fprintf fmt "%s%a" wrapper (term_aux ~fragile ~simplify) ty

  and pp_app ~fragile fmt f args =
    let f, args = get_variant f args in
    match get_status f, args with
    | None, [] ->
      Format.fprintf fmt "@[<hov>%a@]" (term_aux ~fragile:false ~simplify:true) f
    | None, _ ->
      Format.fprintf fmt "@[<hov>(%a %a)@]" (term_aux ~fragile:false ~simplify:true) f
        CCFormat.(list ~sep:(return "@ ") (term_aux ~fragile:true ~simplify:true)) args
    | Some Pretty.Prefix, _ ->
      Format.fprintf fmt "@[<hov>%s%a %a%s@]"
        (if fragile then "(" else "")
        (term_aux ~fragile:false ~simplify:true) f
        CCFormat.(list ~sep:(return "@ ") (term_aux ~fragile:false ~simplify:true)) args
        (if fragile then ")" else "")
    | Some Pretty.Infix, _ ->
      let sep fmt () = Format.fprintf fmt "@ %a " (term_aux ~fragile:true ~simplify:true) f in
      Format.fprintf fmt "@[<hov>(%a)@]"
        CCFormat.(list ~sep (term_aux ~fragile:true ~simplify:true)) args

  and type_quant ~fragile fmt name v body =
    Format.fprintf fmt "%s%s (%a : %a => %a)%s"
      (if fragile then "(" else "")
      name id v
      (term_aux ~fragile:false ~simplify:true) v.Expr.id_type
      (term_aux ~fragile:false ~simplify:true) body
      (if fragile then ")" else "")

  and quant ~fragile fmt name v body =
    let ty = v.Expr.id_type in
    if Term.Reduced.equal Term._Type ty then
      type_quant ~fragile fmt (Format.asprintf "%stype" name) v body
    else begin
      Format.fprintf fmt "%s%s %a (%a => %a)%s"
        (if fragile then "(" else "")
        name (term_aux ~fragile:true ~simplify:true) ty
        var_type v
        (term_aux ~fragile:false ~simplify:true) body
        (if fragile then ")" else "")
    end

  and var_list sep fmt l =
    assert (l <> []);
    let sep fmt () = Format.fprintf fmt " %s@ " sep in
    CCFormat.hvbox (CCFormat.(list ~sep var_type)) fmt l

  and var_type fmt v =
    let ty = v.Expr.id_type in
    Format.fprintf fmt "%a: @[<hov 2>%a@]"
      id v (type_aux ~simplify:true) ty

  let term fmt t =
    Term.disambiguate t;
    (CCFormat.hovbox (term_aux ~fragile:false ~simplify:true)) fmt t

  let fragile fmt t =
    Term.disambiguate t;
    (CCFormat.hovbox (term_aux ~fragile:true ~simplify:false)) fmt t

end

(* Printing contexts *)
(* ************************************************************************ *)

let init fmt opt =
  Format.fprintf fmt
    "@\n(;@[<v>@ %s@ Input file: %s@]@ ;)@]@\n@."
    "Proof automatically generated by Archsat"
    Options.(input_to_string opt.input.file)

let declare_loc fmt = function
  | None ->
    Format.fprintf fmt "(; Implicitly declared ;)"
  | Some l ->
    Format.fprintf fmt "(; @[<hov>%a@] ;)" Dolmen.ParseLocation.fmt l

let declare_id ?loc fmt id =
  Term.disambiguate id.Expr.id_type;
  Format.fprintf fmt "%a@\n%a.@\n@."
    declare_loc loc Print.var_type id

let declare_hyp ?loc fmt id =
  Term.disambiguate id.Expr.id_type;
  Format.fprintf fmt "%a@\n%a.@\n@."
    declare_loc loc Print.var_type id

let declare_goal_term ?loc fmt id =
  Format.fprintf fmt "%a@\n@[<v 2>@[<hv 2>def@ %a :@ logic.proof %a@ :=@]@\n"
    declare_loc loc Print.id id Print.fragile id.Expr.id_type

let proof_term_context pp fmt x =
  Format.fprintf fmt "%a@].@." pp x

