module ContextFreeGrammarsTest
open FStar.String

let rec string_pow (s: string) (n: nat) = 
  match n with
  | 0 -> ""
  | _ -> s ^ string_pow s (n - 1)

let string_length (s: string) = String.length s

// The two languages
// {0^n 1^n | n >= 1} 
type l1 (k: pos) = 
  s: string{s == string_pow "0" k ^ string_pow "1" k}

// P -> 01 | 0 P 1 
type zero_one = s: string{s == "01"}
type zero = s: string{s == "0"}
type one = s: string{s == "1"}
type l2 = 
  | Symbol of zero_one
  | Production of zero * l2 * one

// Functions
let rec length_l2 (s: l2)
  : n: nat{n >= 2}
  = match s with
    | Symbol _ -> 2
    | Production (_, s', _) -> 2 + length_l2 s'

let rec to_string (s: l2)
  : string
  = match s with
    | Symbol k -> k
    | Production (_, s', _) -> "0" ^ to_string s' ^ "1"

// Testing and lemmas
let (f1: l2) = Production ("0", Symbol "01", "1")
let f1_string _
  : Lemma (ensures to_string f1 == "0011")
  = normalize_term_spec (to_string f1)
let f1_string_length _
  : Lemma (ensures length_l2 f1 == 4)
  = normalize_term_spec (length_l2 f1)

let (f2: l1 2) = string_pow "0" 2 ^ string_pow "1" 2
let lemma f2_string _ 
  : Lemma (ensures f2 == "0011")
  = normalize_term_spec (f2)

let rec l2_length_even (s: l2)
  : Lemma (ensures length_l2 s % 2 == 0)
  = match s with
    | Symbol _ -> ()
    | Production (_, s', _) -> l2_length_even s'