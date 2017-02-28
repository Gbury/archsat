
(* All extensions *)
(* ************************************************************************ *)

module type S = sig
  val register : unit -> unit
end

let all_exts = [
  (module Inst                : S);
  (module Ext_stats           : S);
  (module Ext_eq              : S);
  (module Ext_meta            : S);
  (module Ext_prop            : S);
  (module Ext_logic           : S);
  (module Ext_arith           : S);
  (module Ext_prenex          : S);
  (module Ext_skolem          : S);
  (module Ext_functions       : S);
  (module Ext_constraints     : S);
  (module Ext_rewrite         : S);
]

let register_all () =
  List.iter (fun (module E : S) ->
      E.register ()) all_exts

