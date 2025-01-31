module InsertionSort

let rec length (xs: list int)
  : Tot nat (decreases xs) 
  = match xs with
    | [] -> 0
    | _ :: xs' -> 1 + length xs'

let rec ordered (xs: list int)
  : bool
  = match xs with
    | [] -> true
    | [_] -> true
    | x :: y :: xs' -> (x <= y) && ordered (y :: xs')

let rec insert (x: int) (xs: list int)
  : list int
  = match xs with
    | [] -> [x]
    | x' :: xs' ->
      if x <= x' then x :: x' :: xs'
      else x' :: insert x xs'

let rec insert_preserves_order (x: int) (xs: list int)
  : Lemma (requires ordered xs)
          (ensures ordered (insert x xs))
  = match xs with
    | [] -> ()
    | x' :: xs' -> insert_preserves_order x xs'

let rec sort (xs: list int)
  : Tot (list int)
  = match xs with
    | [] -> []
    | x :: xs' -> insert x (sort xs')

let rec sort_ensures_ordered (xs: list int)
  : Lemma (ensures ordered (sort xs))
  = match xs with
    | [] -> ()
    | x :: xs' -> 
      sort_ensures_ordered xs';
      insert_preserves_order x (sort xs')

let rec count (x: int) (xs: list int) 
  : Tot nat (decreases (length xs))
  = match xs with
    | [] -> 0
    | x' :: xs' ->
      (if x = x' then 1 else 0) + count x xs'

let rec count_insert (x y: int) (xs: list int)
  : Lemma (ensures 
            count x (insert y xs) == 
            (if x = y then 1 else 0) + count x xs)
  = match xs with
    | [] -> ()
    | x' :: xs' -> count_insert x y xs'

let rec count_sort (x: int) (xs: list int)
  : Lemma (ensures count x xs == count x (sort xs))
  = match xs with
    | [] -> ()
    | x' :: xs' -> 
      count_insert x x' (sort xs');
      count_sort x xs'