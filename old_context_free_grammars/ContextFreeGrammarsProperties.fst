module ContextFreeGrammarsProperties
open FStar.List
open FStar.String
open ContextFreeGrammars

type yep = 
  | POS of int
  | NEG of int

let rec remove_negative (xs: list yep)
  : Tot (list yep) (decreases xs)
  = match xs with
    | [] -> []
    | POS x :: xs' -> POS x :: remove_negative xs'
    | NEG x :: xs' -> remove_negative xs' 

let rec is_positive (xs: list yep)
  : Tot (bool) (decreases xs)
  = match xs with
    | [] -> true
    | POS _ :: xs' -> is_positive xs'
    | NEG _ :: _ -> false

let rec t (xs: list yep)
  : Lemma (ensures is_positive (remove_negative xs))
  = match xs with
    | [] -> ()
    | _ :: xs' -> t xs'

// Properties
let no_eps_symbol (cfg: cfg_type)
  : bool 
  = not (List.contains (Term "") cfg.terminals) &&
    for_all (
      fun (_, rhs) -> 
        not (List.contains (T (Term "")) rhs)
    ) cfg.productions

let rec check (rhs: rhs_type)
  : Tot (bool) (decreases rhs)
  = match rhs with
    | [] -> true
    | V _ :: rhs' -> true && check rhs'
    | T _ :: rhs' -> false 

let rec no_unit_productions' (productions: list production_type)
  : bool
  = match productions with
    | [] -> true
    | [_, [V _]] -> false
    | _ :: productions' -> no_unit_productions' productions'

let no_unit_productions (cfg: cfg_type)
  : bool 
  = no_unit_productions' cfg.productions

// Construction for a
let rec convert_AST_a_to_AST (ast_a: ast_type) (cfg: cfg_type)
  : list ast_type
  = match ast_a with
    | Node (var, [T' t]) -> 
      if List.contains var cfg.variables then 
        [ast_a]
      else 
        [T' t]
    | Node (var, ast_a_list) -> 
        [Node (var, convert_AST_a_to_AST_list ast_a_list cfg)]
    | T' t -> [T' t]
and convert_AST_a_to_AST_list (ast_a_list: list ast_type) (cfg: cfg_type)
  : list ast_type
  = match ast_a_list with 
    | [] -> [] 
    | ast :: ast_a_list' -> 
      List.append (convert_AST_a_to_AST ast cfg) (convert_AST_a_to_AST_list ast_a_list' cfg)

let a_CF_construction_a = {
  variables = [Var "A"; Var "Z0"];
  terminals = [Term "a"; Term "+"];
  productions = [
    (Var "A", [T (Term "a")]);
    (Var "A", [V (Var "A"); V (Var "Z0"); V (Var "A")]);
    (Var "Z0", [T (Term "+")])
  ];
  start = Var "A"
}
let aPaPa_construction_a = 
  Node (Var "A", [
    Node (Var "A", [T' (Term "a")]);
    Node (Var "Z0", [T' (Term "+")]);
    Node (Var "A", [
      Node (Var "A", [T' (Term "a")]);
      Node (Var "Z0", [T' (Term "+")]);
      Node (Var "A", [T' (Term "a")])
    ])
  ])

let ttt _ 
  : Lemma (convert_AST_a_to_AST aPaPa_construction_a a_CFG == [aPaPa])
  = normalize_term_spec (convert_AST_a_to_AST aPaPa_construction_a a_CFG)

let rec ast_to_list (ast: ast_type) 
  : list terminal_type 
  = match ast with 
    | Node (var, ast_list) -> 
      ast_to_list_list ast_list
    | T' t -> [t]
and ast_to_list_list (ast_list: list ast_type)
  : list terminal_type
  = match ast_list with 
    | [] -> []
    | ast :: ast_list' -> 
      List.append (ast_to_list ast) (ast_to_list_list ast_list')

let tttt _ 
  : Lemma (
            ast_to_list aPaPa == [Term "a"; Term "+"; Term "a"; Term "+"; Term "a"] /\
            ast_to_list aPaPa_CNF == [Term "a"; Term "+"; Term "a"; Term "+"; Term "a"]
          )
  = normalize_term_spec (ast_to_list aPaPa);
    normalize_term_spec (ast_to_list aPaPa_CNF)

let rec construction_a_lemma_1 (ast ast_a: ast_type) (cfg cfg_a: cfg_type)
  : Lemma (requires 
            cfg_a == construction_a cfg /\
            ast_in_cfg ast_a cfg_a /\
            [ast] == convert_AST_a_to_AST ast_a cfg
          )
          (ensures ast_to_list ast_a == ast_to_list ast)
  = match ast with 

let construction_a_lemma_2 (ast ast_a: ast_type) (cfg cfg_a: cfg_type)
  : Lemma (requires 
            cfg_a == construction_a cfg /\
            ast_in_cfg ast_a cfg_a /\
            [ast] == convert_AST_a_to_AST ast_a cfg
          )
          (ensures ast_in_cfg ast cfg)
  = ()

// End goal
// let rec cnf_in_original (ast ast_CNF: ast_type) (cfg cfg_CNF: cfg_type)
//   : Lemma (requires 
//             cfg_CNF == entire_construction cfg /\
//             ast_in_cfg ast_CNF cfg_CNF
//           )
//           (ensures 
//             ast == (Cons?.hd (convert_AST_CNF_to_AST ast_CNF cfg)) /\
//             ast_in_cfg ast cfg
//           )
//   = () 