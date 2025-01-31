module ContextFreeGrammars
open FStar.String
open FStar.List

// Helper functions because loading other files does not work
// FIX
let rec for_all (#a: Type) (f: a -> bool) (xs: list a)
  : Tot (bool) (decreases xs)
  = match xs with
    | [] -> true
    | x :: xs' -> f x && for_all f xs'

let rec foldBack (#a #b: Type) (f: b -> a -> a) (ls: list b) (acc: a)
  : a
  = match ls with
    | [] -> acc
    | l :: ls' -> foldBack f ls' (f l acc)

let rec map (#a #b: Type) (f: a -> b) (xs: list a)
  : Tot (list b) (decreases xs)
  = match xs with
    | [] -> []
    | x :: xs' -> f x :: map f xs'

// All the code
type variable_type = 
  | Var of string
type terminal_type = 
  | Term of string
type variables = list variable_type // (finite) set of variables
type terminals = list terminal_type // (finite) set of terminals
type rhs' = 
  | T of terminal_type
  | V of variable_type
type rhs_type = list rhs'
type production_type = variable_type * rhs_type
type start = variable_type

type cfg_type = {
  variables: variables;
  terminals: terminals;
  productions: list production_type;
  start: start
}

let a_CFG = {
  variables = [Var "A"];
  terminals = [Term "a"; Term "+"];
  productions = [
    (Var "A", [T (Term "a")]);
    (Var "A", [V (Var "A"); T (Term "+"); V (Var "A")])
  ];
  start = Var "A"
}

let sound_CFG (cfg: cfg_type)
  : Tot (bool) = 
  cfg.variables <> [] && cfg.terminals <> [] && // Non-empty variables and terminals
  contains cfg.start cfg.variables && // Start is included
  // Production rules makes sense
  for_all (
    fun (var, rhs) -> 
      List.contains var cfg.variables &&
      for_all (
        fun exp -> 
          match exp with
          | V v -> List.contains v cfg.variables
          | T t -> List.contains t cfg.terminals
      ) rhs
  ) cfg.productions

let a_CFG_is_sound_lemma _
  : Lemma (sound_CFG a_CFG)
  = normalize_term_spec (sound_CFG a_CFG)

// construction for (a)
val handle_one_production_a_foldBack: rhs_type -> int -> Tot (rhs_type * list production_type * int)
let rec handle_one_production_a_foldBack (rhs: rhs_type) (count: int)
  : Tot (rhs_type * list production_type * int) (decreases rhs)
  = match rhs with
    | [] -> [], [], count
    | V v :: rhs' -> 
      let (updated_rhs, new_productions, count') = 
        handle_one_production_a_foldBack rhs' count in
      V v :: updated_rhs, new_productions, count'
    | T t :: rhs' -> 
      let newVar = Var ("Z" ^ Prims.string_of_int count) in
      let (updated_rhs, new_productions, count') = 
        handle_one_production_a_foldBack rhs' (count + 1) in
      V newVar :: updated_rhs, (newVar, [T t]) :: new_productions, count'

val handle_one_production_a: production_type -> int -> list production_type * int
let handle_one_production_a ((var, rhs): production_type) (count: int)
  : list production_type * int
  = if List.length rhs >= 2 then 
      let (updated_rhs, new_productions, count') = 
        handle_one_production_a_foldBack rhs count in
      (var, updated_rhs) :: new_productions, count'
    else [(var, rhs)], count

let handle_one_production_a_test_lemma _
  : Lemma (
      handle_one_production_a (Var "A", [V (Var "A"); T (Term "+"); V (Var "A")]) 0 
      == ([(Var "A", [V (Var "A"); V (Var "Z0"); V (Var "A")]); (Var "Z0", [T (Term "+")])], 1)
    )
  = normalize_term_spec (handle_one_production_a (Var "A", [V (Var "A"); T (Term "+"); V (Var "A")]) 0)

let rec handle_all_productions_a (productions: list production_type) (count: int)
  : Tot (list production_type * int) (decreases productions)
  = match productions with
  | [] -> [], count
  | (var, rhs) :: productions' -> 
    let (new_productions, count') = 
      handle_one_production_a (var, rhs) count in 
    let (res, count'') = handle_all_productions_a productions' count' in
    List.append new_productions res, count''

let handle_all_productions_a_test_lemma _ 
  : Lemma (
      handle_all_productions_a [(Var "A", [T (Term "a")]); (Var "A", [V (Var "A"); T (Term "+"); V (Var "A")])] 0
      == ([(Var "A", [T (Term "a")]); (Var "A", [V (Var "A"); V (Var "Z0"); V (Var "A")]); (Var "Z0", [T (Term "+")])], 1)
    )
  = normalize_term_spec (handle_all_productions_a [(Var "A", [T (Term "a")]); (Var "A", [V (Var "A"); T (Term "+"); V (Var "A")])] 0)

// Does *not* return a vaild CFG at the moment
let construction_a (cfg: cfg_type) 
    : cfg_type 
    = 
      let (new_productions, _) = handle_all_productions_a cfg.productions 0 in 
      let cfg' = { cfg with productions = new_productions } in
      let updated_variables = map (fun (var, _) -> var) cfg'.productions in
      { cfg' with variables = updated_variables }

// Construction for (b)
// fix the syntax here
let rec handle_one_production_b (var_rhs: production_type) (count: int)
  : Tot (list production_type * int ) (decreases snd var_rhs)
  = let (var, rhs) = var_rhs in 
    match rhs with
    | [] -> [], count
    | [T t] -> [(var, [T t])], count
    | [x; y] -> [(var, [x; y])], count
    | v :: rhs' -> 
      let cVar = Var ("C" ^ Prims.string_of_int count) in
      let (res, count') = handle_one_production_b (cVar, rhs') (count + 1) in
      (var, [v; V cVar]) :: res, count'

let handle_one_production_b_test_lemma _ 
  : Lemma (
      handle_one_production_b (Var "A", [V (Var "A"); V (Var "Z0"); V (Var "A")]) 0
      == ([(Var "A", [V (Var "A"); V (Var "C0")]); (Var "C0", [V (Var "Z0"); V (Var "A")])], 1)
  )
  = normalize_term_spec (handle_one_production_b (Var "A", [V (Var "A"); V (Var "Z0"); V (Var "A")]) 0)

let rec handle_all_productions_b (productions: list production_type) (count: int)
  : list production_type * int 
  = match productions with
    | [] -> [], count
    | (var, rhs) :: productions' -> 
      if List.length rhs >= 2 then
        let (new_productions, count') = handle_one_production_b (var, rhs) count in 
        let (new_productions', count'') = handle_all_productions_b productions' count' in
        List.append new_productions new_productions', count''
      else 
        let (new_productions', count'') = handle_all_productions_b productions' count in
        (var, rhs) :: new_productions', count''

let construction_b (cfg: cfg_type)
  : cfg_type
  = 
    let (updated_productions, _) = handle_all_productions_b cfg.productions 0 in
    { cfg with productions = updated_productions }

// Here we also handle the missing variables that came from the two sub constructions
let entire_construction (cfg: cfg_type)
  : cfg_type
  = 
    let cfg' = construction_b (construction_a cfg) in
    let updated_variables = map (fun (var, _) -> var) cfg'.productions in 
    { cfg' with variables = updated_variables }

let (a_CFG_CNF: cfg_type) = {
  variables = [Var "A"; Var "A"; Var "C0"; Var "Z0"]; // Temporary testing
  terminals = [Term "a"; Term "+"];
  productions =
    [(Var "A", [T (Term "a")]); (Var "A", [V (Var "A"); V (Var "C0")]);
    (Var "C0", [V (Var "Z0"); V (Var "A")]); (Var "Z0", [T (Term "+")])];
  start = Var "A"
}

let entire_construction_test_lemma _ 
  : Lemma (a_CFG_CNF == entire_construction a_CFG)
  = normalize_term_spec (entire_construction a_CFG)

// Abstract syntax tree
type ast_type = 
  | Node of variable_type * list ast_type
  | T' of terminal_type

let aPaPa = 
    Node (Var "A", [
      Node (Var "A", [T' (Term "a")]);
      T' (Term "+");
      Node (Var "A", [
        Node (Var "A", [T' (Term "a")]);
        T' (Term "+");
        Node (Var "A", [T' (Term "a")])
      ])
  ])

let aPaPa_CNF = 
  Node (Var "A", [
    Node (Var "A", [T' (Term "a")]);
    Node (Var "C0", [
      Node (Var "Z0", [T' (Term "+")]);
      Node (Var "A", [
        Node (Var "A", [T' (Term "a")]);
        Node (Var "C0", [
          Node (Var "Z0", [T' (Term "+")]);
          Node (Var "A", [T' (Term "a")])
        ])
      ])
    ])
  ])

let rec print_AST (ast: ast_type)
  : string 
  = match ast with
    | Node (var, ast_list) -> print_AST_list ast_list
    | T' (Term t) -> t
and print_AST_list (ast_list: list ast_type)
  : string 
  = match ast_list with
    | [] -> ""
    | ast :: ast_list' -> 
      print_AST ast ^ print_AST_list ast_list'

let aPaPa_string_lemma _
  : Lemma (print_AST aPaPa == "a+a+a" /\ print_AST aPaPa_CNF == "a+a+a")
  = normalize_term_spec (print_AST aPaPa);
    normalize_term_spec (print_AST aPaPa_CNF)

let rec get_production_rhs_from_AST (ast_list: list ast_type)
  : rhs_type 
  = match ast_list with
    | [] -> []
    | Node (var, _) :: ast_list' -> V var :: get_production_rhs_from_AST ast_list'
    | T' term :: ast_list' -> T term :: get_production_rhs_from_AST ast_list'

let rec ast_in_cfg (ast: ast_type) (cfg: cfg_type)
  : bool
  = match ast with
    | Node (var, ast_list) -> 
      let rhs = get_production_rhs_from_AST ast_list in
      List.contains var cfg.variables && List.contains (var, rhs) cfg.productions &&
      ast_in_cfg_list ast_list cfg
    | T' t -> true // valid since we use get_production_rhs_from_AST and checks above if it is a production rule
and ast_in_cfg_list (ast_list: list ast_type) (cfg: cfg_type)
  : bool
  = match ast_list with
    | [] -> true
    | ast :: ast_list' -> ast_in_cfg ast cfg && ast_in_cfg_list ast_list' cfg

let aPaPa_in_a_CFG_lemma _ 
  : Lemma (ast_in_cfg aPaPa a_CFG == true)
  = normalize_term_spec (ast_in_cfg aPaPa a_CFG)

// Word in CNF to word in orginal
let rec get_vars_from_productions (productions: list production_type)
    : Tot (list variable_type) (decreases productions)
    = match productions with
      | [] -> []
      | (var, _) :: productions' -> var :: get_vars_from_productions productions'

let rec convert_AST_CNF_to_AST (ast_CNF: ast_type) (cfg: cfg_type) 
  : Tot (list ast_type) (decreases ast_CNF)
  = match ast_CNF with 
    | Node (var, ast_CNF_list) -> 
        if List.contains var (get_vars_from_productions cfg.productions) then 
            [Node (var, convert_AST_CNF_to_AST_list ast_CNF_list cfg)]
        else
            convert_AST_CNF_to_AST_list ast_CNF_list cfg
    | T' t -> [T' t]
and convert_AST_CNF_to_AST_list (ast_CNF_list: list ast_type) (cfg: cfg_type)
  : Tot (list ast_type) (decreases ast_CNF_list)
  = match ast_CNF_list with
    | [] -> []
    | ast :: ast_CNF_list' -> 
        List.append (convert_AST_CNF_to_AST ast cfg) (convert_AST_CNF_to_AST_list ast_CNF_list' cfg)

let aPaPa' = Cons?.hd (convert_AST_CNF_to_AST aPaPa_CNF a_CFG)
let convert_CNF_to_original_test_lemma _ 
  : Lemma (ensures aPaPa == aPaPa')
  = normalize_term_spec (Cons?.hd (convert_AST_CNF_to_AST aPaPa_CNF a_CFG))