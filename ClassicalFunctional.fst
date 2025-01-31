module ClassicalFunctional
let rec length (#a: Type) (l: list a)
  : Tot nat (decreases l) = 
  match l with
  | [] -> 0
  | _ :: l' -> 1 + length l'

val append #a (xs ys: list a) 
  : l: list a {length l = length xs + length ys}
let rec append xs ys = 
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys

let rec append_two_lists (#a: Type) (xs ys: list a)
  : Lemma (length (append xs ys) == length xs + length ys)
  = match xs with
  | [] -> ()
  | _ :: xs' -> append_two_lists xs' ys

let rec append_associative #a (ls xs ys: list a)
  : Lemma (ensures append (append ls xs) ys == append ls (append xs ys))
  = match ls with
  | [] -> ()
  | l :: ls' -> append_associative ls' xs ys

let rec reverse (#a: Type) (l:list a)
  : list a
  = match l with
  | [] -> []
  | hd :: tl -> append (reverse tl) [hd]

let rec foldLeft #a #b (f: b -> a -> a) (ls: list b) (acc:a)
  : a
  = match ls with
  | [] -> acc
  | l :: ls' -> foldLeft f ls' (f l acc)

let rec sum (xs: list int)
  : Tot int (decreases xs)
  = match xs with
  | [] -> 0
  | x :: xs' -> x + sum xs'

let rec foldLeft_and_sum_general (acc: int) (xs: list int)
  : Lemma (ensures foldLeft (+) xs acc == acc + sum xs)
          (decreases length xs)
  = match xs with
  | [] -> ()
  | x :: xs' -> foldLeft_and_sum_general (x + acc) xs'
  
let foldLeft_and_sum (xs: list int)
  : Lemma (ensures foldLeft (+) xs 0 == sum xs)
  = foldLeft_and_sum_general 0 xs

let rec append_list_on_empty (#a: Type) (ls: list a)
  : Lemma (append ls [] == ls)
  = match ls with
  | [] -> ()
  | _ :: ls' -> append_list_on_empty ls'

let rec foldLeft_cons_is_rev_general (#a: Type) (ls xs: list a)
  : Lemma (ensures foldLeft Cons ls xs == append (reverse ls) xs)
  = match ls with
  | [] -> ()
  | l :: ls' -> 
    append_associative (reverse ls') [l] xs;
    foldLeft_cons_is_rev_general ls' (l :: xs)

let foldLeft_Cons_is_rev (#a: Type) (ls: list a)
  : Lemma (foldLeft Cons ls [] == reverse ls)
  = append_list_on_empty (reverse ls);
    foldLeft_cons_is_rev_general ls []