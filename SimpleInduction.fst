module SimpleInduction
open FStar.Mul

let rec sum1 (n: nat)
  : nat
  = match n with
    | 0 -> 0
    | _ -> n + sum1 (n - 1)

let rec sum1_value (n: nat)
  : Lemma (sum1 n == n * (n + 1) / 2)
  = match n with
    | 0 -> ()
    | _ -> sum1_value (n - 1)