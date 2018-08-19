(* This file is free software, part of Archsat. See file "LICENSE" for more details. *)

(* Module aliases *)
(* ************************************************************************ *)

module Infix = struct
  module G = QCheck.Gen
  module I = QCheck.Iter
  module S = QCheck.Shrink
end
open Infix

(* Common interface for value generation *)
(* ************************************************************************ *)

module type S = sig
  type t
  val print : t -> string
  val small : t -> int
  val shrink : t S.t
  val sized : t G.sized
  val gen : t G.t
  val t : t QCheck.arbitrary
  val make : t G.t -> t QCheck.arbitrary
end

(* Helper functions *)
(* ************************************************************************ *)

(* Type for a sequence *)
type 'a seq = ('a -> unit) -> unit

let iter_filter p seq k =
  seq (fun x -> if p x then k x)


(* Splitting functions *)

let rec split size len =
  let open G in
  if len = 0 then
    return []
  else if len = 1 then
    return [size]
  else begin
    (0 -- size) >>= fun hd ->
    split (size - hd) (len - 1) >|= fun tl ->
    hd :: tl
  end

let split_int size =
  G.(split size 2 >|= function
    | [a; b] -> a, b | _ -> assert false)

let sublist l =
  G.(shuffle_l l >>= fun l ->
     (0 -- List.length l) >|= fun n ->
     CCList.take n l)

