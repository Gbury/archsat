(*
Copyright (c) 2013, Simon Cruanes
All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.  Redistributions in binary
form must reproduce the above copyright notice, this list of conditions and the
following disclaimer in the documentation and/or other materials provided with
the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

(** {1 TPTP Ast} *)

exception ParseError of ParseLocation.t

type name =
  | NameInt of int
  | NameString of string
  (** name of a formula *)
and role =
  | R_axiom       (* true *)
  | R_hypothesis  (* true *)
  | R_definition  (* symbol definition *)
  | R_assumption  (* true, but must be proved before *)
  | R_lemma       (* must be proved before use *)
  | R_theorem     (* must be proved before use *)
  | R_conjecture  (* to be proven *)
  | R_negated_conjecture  (* negation of conjecture, must prove 'false' *)
  | R_plain       (* no specific semantics (proof...) *)
  | R_finite of string   (* finite interpretation, don't care *)
  | R_question    (* existential question *)
  | R_type        (* type declaration *)
  | R_unknown     (* error *)
  (** formula role *)
and optional_info = general_data list
and general_data =
  | GString of string
  | GVar of string   (* variable *)
  | GInt of int
  | GColumn of general_data * general_data
  | GNode of string * general_data list
  | GList of general_data list

let role_of_string = function
  | "axiom" -> R_axiom
  | "hypothesis" -> R_hypothesis
  | "definition" -> R_definition
  | "assumption" ->  R_assumption
  | "lemma" -> R_lemma
  | "theorem" -> R_theorem
  | "conjecture" -> R_conjecture
  | "negated_conjecture" -> R_negated_conjecture
  | "plain" -> R_plain
  | "fi_domain" -> R_finite "domain"
  | "fi_functors" -> R_finite "functors"
  | "fi_predicates" -> R_finite "predicates"
  | "question" -> R_question
  | "type" -> R_type
  | "unknown" -> R_unknown
  | s -> failwith ("not a proper TPTP role: " ^ s)

let string_of_role = function
  | R_axiom -> "axiom"
  | R_hypothesis -> "hypothesis"
  | R_definition -> "definition"
  | R_assumption -> "assumption"
  | R_lemma -> "lemma"
  | R_theorem -> "theorem"
  | R_conjecture -> "conjecture"
  | R_negated_conjecture -> "negated_conjecture"
  | R_plain -> "plain"
  | R_finite what -> "fi_" ^ what
  | R_question -> "question"
  | R_type -> "type"
  | R_unknown -> "unknown"

let pp_role buf r =
  Buffer.add_string buf (string_of_role r)

let fmt_role fmt r =
  Format.pp_print_string fmt (string_of_role r)

let string_of_name = function
  | NameInt i -> string_of_int i
  | NameString s -> s

let pp_name buf n =
  Buffer.add_string buf (string_of_name n)

let fmt_name fmt n =
  Format.pp_print_string fmt (string_of_name n)

let rec pp_list ?(sep=", ") pp_item buf = function
  | x::((y::xs) as l) ->
    pp_item buf x;
    Buffer.add_string buf sep;
    pp_list ~sep pp_item buf l
  | x::[] -> pp_item buf x
  | [] -> ()

let rec pp_general buf d = match d with
  | GString s -> Buffer.add_string buf s
  | GInt i -> Printf.bprintf buf "%d" i
  | GVar s -> Buffer.add_string buf s
  | GColumn (a, b) -> Printf.bprintf buf "%a: %a" pp_general a pp_general b
  | GNode (f, l) ->
    Printf.bprintf buf "%s(%a)" f (pp_list pp_general) l
  | GList l ->
    Printf.bprintf buf "[%a]" (pp_list pp_general) l

let rec pp_general_debug buf d = match d with
  | GString s -> Printf.bprintf buf "GSstr %s" s
  | GInt i -> Printf.bprintf buf "GInt %d" i
  | GVar s -> Printf.bprintf buf "GVar %s" s
  | GColumn (a, b) -> Printf.bprintf buf "%a: %a" pp_general_debug a pp_general_debug b
  | GNode (f, l) ->
    Printf.bprintf buf "GNode(%s[%a])" f (pp_list pp_general_debug) l
  | GList l ->
    Printf.bprintf buf "[%a]" (pp_list pp_general_debug) l

let sprintf format =
  let buffer = Buffer.create 64 in
  Printf.kbprintf
    (fun fmt -> Buffer.contents buffer)
    buffer
    format

let fmt_general fmt d =
  Format.pp_print_string fmt (sprintf "%a" pp_general d)

let list_pp ?(start="[") ?(stop="]") ?(sep=", ") pp_item buf l =
  let rec print l = match l with
    | x::((_::_) as l) ->
      pp_item buf x;
      Buffer.add_string buf sep;
      print l
    | x::[] -> pp_item buf x
    | [] -> ()
  in Buffer.add_string buf start; print l; Buffer.add_string buf stop

let pp_generals buf l = list_pp pp_general buf l

let list_print ?(start="[") ?(stop="]") ?(sep=", ") pp_item fmt l =
  let rec print fmt l = match l with
    | x::((_::_) as l) ->
      pp_item fmt x;
      Format.pp_print_string fmt sep;
      Format.pp_print_cut fmt ();
      print fmt l
    | x::[] -> pp_item fmt x
    | [] -> ()
  in
  Format.pp_print_string fmt start;
  print fmt l;
  Format.pp_print_string fmt stop

let fmt_generals fmt l = list_print fmt_general fmt l

module type S = sig
  type hoterm
  type form
  type ty

  type t =
    | CNF of name * role * form list * optional_info
    | FOF of name * role * form * optional_info
    | TFF of name * role * form * optional_info
    | THF of name * role * hoterm * optional_info  (* XXX not parsed yet *)
    | TypeDecl of name * string * ty  (* type declaration for a symbol *)
    | NewType of name * string * ty (* declare new type constant... *)
    | Include of string
    | IncludeOnly of string * name list   (* include a subset of names *)
    (** top level declaration *)

  type declaration = t

  val get_name : t -> name
    (** Find the name of the declaration, or
        @raise Invalid_argument if the declaration is an include directive *)

  class ['a] visitor : object
    method clause : 'a -> role -> form list -> 'a
    method fof : 'a -> role -> form -> 'a
    method tff : 'a -> role -> form -> 'a
    method thf : 'a -> role -> hoterm -> 'a
    method any_form : 'a -> role -> form -> 'a
    method tydecl : 'a -> string -> ty -> 'a
    method new_ty : 'a -> string -> ty -> 'a
    method include_ : 'a -> string -> 'a
    method include_only : 'a -> string -> name list -> 'a
    method visit : 'a -> t -> 'a
  end

  val map :
    ?form:(form -> form) ->
    ?hoterm:(hoterm -> hoterm) ->
    t -> t
  (** Map terms to other terms *)

end

module Untyped = struct
  type hoterm = Expr.Untyped.term
  type form = Expr.Untyped.term
  type ty = Expr.Untyped.term

  type t =
    | CNF of name * role * form list * optional_info
    | FOF of name * role * form * optional_info
    | TFF of name * role * form * optional_info
    | THF of name * role * hoterm * optional_info  (* XXX not parsed yet *)
    | TypeDecl of name * string * ty  (* type declaration for a symbol *)
    | NewType of name * string * ty (* declare new type constant... *)
    | Include of string
    | IncludeOnly of string * name list   (* include a subset of names *)
    (** top level declaration *)

  type declaration = t

  let get_name = function
    | CNF (n, _, _, _) -> n
    | FOF (n, _, _, _) -> n
    | TFF (n, _, _, _) -> n
    | THF (n, _, _, _) -> n
    | TypeDecl (n, _, _) -> n
    | NewType (n, _, _) -> n
    | IncludeOnly _
    | Include _ ->
      raise (Invalid_argument "Ast_tptp.name_of_decl: include directive has no name")

  class ['a] visitor = object (self)
    method clause (acc:'a) _r _c = acc
    method fof (acc:'a) _r _f = acc
    method tff (acc:'a) _r _f = acc
    method thf (acc:'a) _r _f = acc
    method any_form (acc:'a) _r _f = acc
    method tydecl (acc:'a) _s _ty = acc
    method new_ty (acc:'a) _s _ty = acc
    method include_ (acc:'a) _file = acc
    method include_only (acc:'a) _file _names = acc
    method visit (acc:'a) decl = match decl with
      | CNF (_, r, c, _) -> self#clause acc r c
      | FOF (_, r, f, _) -> self#any_form (self#fof acc r f) r f
      | TFF (_, r, f, _) -> self#any_form (self#tff acc r f) r f
      | THF (_, r, f, _) -> self#thf acc r f
      | TypeDecl (_, s, ty) -> self#tydecl acc s ty
      | NewType (_, s, ty) -> self#new_ty acc s ty
      | Include f -> self#include_ acc f
      | IncludeOnly (f,names) -> self#include_only acc f names
  end

  let __id f = f

  let map ?(form=__id) ?(hoterm=__id) = function
    | CNF (n,r,c,i) -> CNF(n,r, List.map form c, i)
    | FOF (n,r,f,i) -> FOF(n,r, form f, i)
    | TFF (n,r,f,i) -> TFF(n,r, form f, i)
    | THF (n,r,f,i) -> THF(n,r, hoterm f, i)
    | (TypeDecl _ | NewType _ | IncludeOnly _ | Include _) as d -> d

end
