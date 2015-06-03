
type divisor = {
  prime : Z.t;
  power : int;
}

val value : divisor -> Z.t

val decomposition : Z.t -> divisor list

