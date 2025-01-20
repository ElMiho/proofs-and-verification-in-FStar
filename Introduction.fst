module Introduction
open FStar.Mul

let rec square (xs: list int)
  : list int
  = match xs with
    | [] -> []
    | x :: xs' -> x * x :: square xs'

let rec square' (xs: list int)
  : Tot (list int) (decreases xs)
  = match xs with
    | [] -> []
    | x :: xs' -> x * x :: square' xs'

let rec is_natural_numbers (xs: list int)
  : bool
  = match xs with
    | [] -> true
    | x :: xs' -> x >= 0 && is_natural_numbers xs'

let rec square'_positive (xs: list int)
  : Lemma (ensures is_natural_numbers (square' xs))
  = match xs with
    | [] -> ()
    | _ :: xs' -> square'_positive xs'

let rec length xs
  : nat
  = match xs with
    | [] -> 0
    | _ :: xs' -> 1 + length xs'

let rec ordered (xs: list int)
  : bool
  = match xs with
    | [] -> true
    | [_] -> true
    | x :: y :: xs' -> (x <= y) && ordered (y :: xs')

let rec minS (xs: list int{length xs >= 1})
  : int
  = match xs with
    | [x] -> x
    | x :: xs' -> 
      let s = minS xs' in
      min x s

let rec smallest_is_first (xs: list int)
  : Lemma (requires ordered xs /\ length xs >= 1)
          (ensures Cons?.hd xs == minS xs)
  = match xs with
    | [_] -> ()
    | _ :: xs' -> smallest_is_first xs'