(*
Zipperposition: a functional superposition prover for prototyping
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

module ZTbl = Hashtbl.Make(Z)

type divisor = {
  prime : Z.t;
  power : int;
}

let value d = Z.pow d.prime d.power

let two = Z.of_int 2

(* table from numbers to some of their divisor (if any) *)
let _table = lazy (
  let t = ZTbl.create 256 in
  ZTbl.add t two None;
  t)

let _divisors n = ZTbl.find (Lazy.force _table) n

let _add_prime n =
  ZTbl.replace (Lazy.force _table) n None

(* add to the table the fact that [d] is a divisor of [n] *)
let _add_divisor n d =
  assert (not (ZTbl.mem (Lazy.force _table) n));
  ZTbl.add (Lazy.force _table) n (Some d)

(* primality test, modifies _table *)
let _is_prime n0 =
  let n = ref two in
  let bound = Z.succ (Z.sqrt n0) in
  let is_prime = ref true in
  while !is_prime && Z.leq !n bound do
    if Z.sign (Z.rem n0 !n) = 0
    then begin
      is_prime := false;
      _add_divisor n0 !n;
    end;
    n := Z.succ !n;
  done;
  if !is_prime then _add_prime n0;
  !is_prime

let is_prime n =
  try
    begin match _divisors n with
      | None -> true
      | Some _ -> false
    end
  with Not_found ->
    match Z.probab_prime n 7 with
    | 0 -> false
    | 2 -> (_add_prime n; true)
    | 1 ->
      _is_prime n
    | _ -> assert false

let rec _merge l1 l2 = match l1, l2 with
  | [], _ -> l2
  | _, [] -> l1
  | p1::l1', p2::l2' ->
    match Z.compare p1.prime p2.prime with
    | 0 ->
      {prime=p1.prime; power=p1.power+p2.power} :: _merge l1' l2'
    | n when n < 0 ->
      p1 :: _merge l1' l2
    | _ -> p2 :: _merge l1 l2'

let rec _decompose n =
  try
    begin match _divisors n with
      | None -> [{prime=n; power=1;}]
      | Some q1 ->
        let q2 = Z.divexact n q1 in
        _merge (_decompose q1) (_decompose q2)
    end
  with Not_found ->
    ignore (_is_prime n);
    _decompose n

let decomposition n =
  if is_prime n
  then [{prime=n; power=1;}]
  else _decompose n

let primes_leq n0 k =
  let n = ref two in
  while Z.leq !n n0 do
    if is_prime !n then k !n
  done

