
(* The Dolmen library is used to parse input languages *)
(* ************************************************************************ *)

module P = Dolmen.Logic.Make
    (Dolmen.ParseLocation)
    (Dolmen.Id)
    (Dolmen.Term)
    (Dolmen.Statement)

include P

