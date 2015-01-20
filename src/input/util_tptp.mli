
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

(** {1 Utils related to TPTP} *)

(** {2 Printing/Parsing} *)

exception Parse_error of ParseLocation.t * string

val find_file : string -> string -> string option
  (** [find_file name dir] looks for a file with the given [name],
      recursively, in [dir], or in its parent dir recursively.
      It also looks in the "TPTP" environment variable. *)

val parse_lexbuf : ?names:Ast_tptp.name list ->
                    Lexing.lexbuf -> Ast_tptp.Untyped.t list
  (** Given a lexbuf, try to parse its content into a sequence of untyped
    declarations *)

val parse_file : recursive:bool -> string -> Ast_tptp.Untyped.t list
  (** Parsing a TPTP file is here presented with a [recursive] option
      that, if true, will make "include" directives to be recursively
      parsed. It uses {!find_file} for included files. *)

