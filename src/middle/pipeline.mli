
(** Top-level operator combinators

    This module defines combinators to create and execute top-level
    operators. The main point is to define a main loop to run on parsed
    statements.
*)

(** {2 Type definitions } *)

type ('a, 'b) op
(** An operator from values of type ['a] to value sof type ['b]. *)

type ('a, 'b) t
(** The type of pipelines from values of type ['a] to values of type ['b]. *)

type 'a fix = [ `Ok | `Gen of bool * 'a Gen.t ]
(** Type used to fixpoint expanding statements such as includes. *)

type ('a, 'b) cont = [ `Continue of 'a | `Done of 'b ]
(** Type used for continuation operators, allowing to leave the pipeline early. *)

(** {2 Creating operators} *)

val apply : ?name:string -> ('a -> 'b) -> ('a, 'b) op
(** Create an operator from a function *)

val f_map :
  ?name:string ->
  ?test:('a -> bool) ->
  ('a * 'b -> 'c) ->
  ('a * 'b, ('a * 'c, 'a) cont) op
(** [f_map f] is equivalent to [apply (fun ((opt, y) as x) -> (opt, f x))] *)

val iter_ : ?name:string -> ('a -> unit) -> ('a, 'a) op
(** Perform the function's side-effect and return the same input. *)

(** {2 Creating pipelines} *)

val _end : ('a, 'a) t

val (@>>>) : ('a, 'b) op -> ('b, 'c) t -> ('a, 'c) t
(** Add an operator at the beginning of a pipeline. *)

val (@>|>) : ('a, ('b, 'c) cont) op -> ('b, 'c) t -> ('a, 'c) t
(** Add a continuation operator, allowing to stop evaluation of the
    pipeline early. *)

val (@|||) : ('a, 'b) t -> ('b, 'c) t -> ('a, 'c) t
(** Concatenate two pipeline. Whenever possible it is best to use [(@>>>)],
    which creates tail-rec pipelines. *)

val fix : ('a * 'b, 'a * 'b fix) op -> ('a * 'b, 'a) t -> ('a * 'b, 'a) t
(** Perform a fixpoint expansion *)

(** {2 Evaluating pipelines} *)

val eval : ('a, 'b) t -> 'a -> 'b
(** Evaluate a pipeline to a function. *)

val run :
  ?finally:(Options.opts -> exn option -> Options.opts) ->
  (Options.opts -> 'a option) -> Options.opts ->
  (Options.opts * 'a, Options.opts) t -> Options.opts
(** Loop the evaluation of a pipeline over a generator, and starting options.
    @param finally a function called at the end of every iteration (even if an exception
      has been raised) *)
