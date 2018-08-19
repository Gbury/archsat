(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* The Dolmen library is used to parse input languages *)
(* ************************************************************************ *)

(** See documentation at
    {{:http://gbury.github.io/dolmen/dev/Logic.Make.html} Logic.Make} *)
module P = Dolmen.Logic.Make
    (Dolmen.ParseLocation)
    (Dolmen.Id)
    (Dolmen.Term)
    (Dolmen.Statement)

(** Module inclusion is used to avoid re-writing the correct interface
    at each release of Dolmen. *)
include P

