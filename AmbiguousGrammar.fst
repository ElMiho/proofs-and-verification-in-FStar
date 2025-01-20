module AmbiguousGrammar
open FStar.String

type a_symbol = s: string{s == "a"}
type ambiguous_language = 
  | Symbol of a_symbol
  | Plus of ambiguous_language * ambiguous_language
(* 
A => A + A => A + A + A => a + A + A => a + a + A => a + a + a
A => A + A => A + A + A => A + A + a => ... => a + a + a
and thus ambiguous
*)

type unambiguous_language =
  | Symbol' of a_symbol
  | Plus' of unambiguous_language * a_symbol
(* 
A => A + a => A + a + a => a + a + a
*)