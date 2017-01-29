
type divisor = {
  prime : Z.t;
  power : int;
}

val value : divisor -> Z.t

val decomposition : Z.t -> divisor list

val is_prime : Z.t -> bool

val primes_leq : Z.t -> (Z.t -> unit) -> unit

