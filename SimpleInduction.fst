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

let rec fibonacci (n:nat)
  : nat
  = if n <= 1 then 1 
  else fibonacci (n - 1) + fibonacci (n - 2)

let rec g (a b n : nat)
  : Tot nat (decreases n)
  = match n with
  | 0 -> a
  | _ -> g b (a+b) (n-1)

let rec general_G_relation (a b n: nat)
  : Lemma (ensures
      g a b 0 == a /\ 
      g a b 1 == b /\
      n >= 2 ==> g a b n == g a b (n - 1) + g a b (n - 2)
  )
  (decreases n)
  = match n with
  | 0 -> ()
  | 1 -> ()
  | _ -> 
      general_G_relation b (a + b) (n - 1)

let rec g_is_okay (n: nat)
  : Lemma (ensures g 1 1 n == fibonacci n)
          (decreases n)
  = match n with
  | 0 | 1 -> ()
  | _ ->
      general_G_relation 1 1 n;
      g_is_okay (n - 1);
      g_is_okay (n - 2)