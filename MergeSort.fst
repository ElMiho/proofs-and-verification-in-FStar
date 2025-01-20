module MergeSort

// Helper
// ??? Find a way to make this nicer with imports
let rec length (xs: list int)
  : Tot nat (decreases xs) // Important later with Tot and decreases
  = match xs with
    | [] -> 0
    | _ :: xs' -> 1 + length xs'

let rec ordered (xs: list int)
  : bool
  = match xs with
    | [] -> true
    | [_] -> true
    | x :: y :: xs' -> (x <= y) && ordered (y :: xs')

let rec count (x: int) (xs: list int) 
  : Tot nat (decreases (length xs))
  = match xs with
    | [] -> 0
    | x' :: xs' ->
      (if x = x' then 1 else 0) + count x xs'
      
val append (xs ys: list int) 
  : l: list int {length l = length xs + length ys}
let rec append xs ys = 
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys

// Merge sort 
let rec split (xs: list int)
  : Tot (list int * list int) (decreases xs)
  = match xs with
    | [] -> [], []
    | [x0] -> [x0], []
    | x0 :: x1 :: xs' -> 
      let xEven, xOdd = split xs' in 
      x0 :: xEven, x1 :: xOdd

let rec split_length_lemma (xs xEven xOdd: list int)
  : Lemma (requires (xEven, xOdd) == split xs)
          (ensures length xs == length xEven + length xOdd)
          (decreases (length xs))
  = match xs with
    | [] | [_] -> ()
    | _ :: _ :: xs' -> 
      let (xEven', xOdd') = split xs' in
      split_length_lemma xs' xEven' xOdd'

let rec split_length_smaller_lemma (xs xEven xOdd: list int)
  : Lemma (requires 
            length xs >= 2 /\
            (xEven, xOdd) == split xs)
          (ensures 
            length xEven < length xs /\
            length xOdd < length xs)
  = match xs with
    | [_; _] -> ()
    | [_; _; _] -> ()
    | x0 :: x1 :: xs' -> 
      let (xEven', xOdd') = split xs' in
      split_length_smaller_lemma xs' xEven' xOdd'

let rec split_count_lemma (e: int) (xs xEven xOdd: list int)
  : Lemma (requires (xEven, xOdd) == split xs)
          (ensures count e xs == count e xEven + count e xOdd)
  = match xs with
    | [] -> ()
    | [_] -> ()
    | _ :: _ :: xs' -> 
      let xEven', xOdd' = split xs' in
      split_count_lemma e xs' xEven' xOdd'

let rec merge (xs ys: list int)
  : Tot (list int) (decreases length (append xs ys))
  = match xs, ys with
    | [], [] -> []
    | xs, [] -> xs
    | [], ys -> ys
    | x :: xs', y :: ys' -> 
      if x <= y then x :: merge xs' ys
      else y :: merge xs ys'

let rec merge_ordered_lemma (xs ys: list int)
  : Lemma (requires ordered xs /\ ordered ys)
          (ensures ordered (merge xs ys))
          (decreases length (append xs ys))
  = match xs, ys with
    | [], [] -> ()
    | _, [] | [], _ -> ()
    | _ :: xs', _ :: ys' -> 
      merge_ordered_lemma xs' ys;
      merge_ordered_lemma xs ys'

let rec merge_count_lemma (e: int) (xs ys: list int)
  : Lemma (ensures count e xs + count e ys == count e (merge xs ys))
  = match xs, ys with
    | [], [] -> ()
    | _, [] | [], _ -> ()
    | _ :: xs', _ :: ys' -> 
      merge_count_lemma e xs ys';
      merge_count_lemma e xs' ys

let rec merge_length_lemma (xs ys: list int)
  : Lemma (ensures length (merge xs ys) == length xs + length ys)
          (decreases length (append xs ys))
  = match xs, ys with
    | [], [] -> ()
    | _, [] | [], _ -> ()
    | _ :: xs', _ :: ys' -> 
      merge_length_lemma xs' ys;
      merge_length_lemma xs ys'

let rec sort (xs: list int)
  : Tot (list int) (decreases (length xs))
  = match xs with
    | [] -> []
    | [x] -> [x]
    | _ -> 
      let xEven, xOdd = split xs in
      split_length_smaller_lemma xs xEven xOdd;
      merge (sort xEven) (sort xOdd)

let rec sort_ensures_ordered (xs: list int)
  : Lemma (ensures ordered (sort xs))
          (decreases length xs)
  = match xs with 
    | [] -> ()
    | [_] -> ()
    | _ -> 
      let xEven, xOdd = split xs in
      split_length_smaller_lemma xs xEven xOdd;
      sort_ensures_ordered xEven;
      sort_ensures_ordered xOdd;
      merge_ordered_lemma (sort xEven) (sort xOdd)

let rec sort_preserves_length (xs: list int)
  : Lemma (ensures length xs == length (sort xs))
          (decreases (length xs))
  = match xs with
    | [] -> ()
    | [_] -> ()
    | _ -> 
      let xEven, xOdd = split xs in
      split_length_smaller_lemma xs xEven xOdd;
      merge_length_lemma (sort xEven) (sort xOdd);
      split_length_lemma xs xEven xOdd;
      sort_preserves_length xEven;
      sort_preserves_length xOdd

let rec sort_count_lemma (e: int) (xs: list int)
  : Lemma (ensures count e xs == count e (sort xs))
          (decreases length xs)
  = match xs with
    | [] -> ()
    | [_] -> ()
    | _ -> 
      let xEven, xOdd = split xs in
      merge_count_lemma e (sort xEven) (sort xOdd);
      split_length_smaller_lemma xs xEven xOdd;
      sort_preserves_length xEven;
      sort_preserves_length xOdd;
      sort_count_lemma e (sort xEven);
      sort_count_lemma e (sort xOdd)