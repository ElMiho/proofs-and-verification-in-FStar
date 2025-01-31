module NewContextFreeGrammars
open FStar.List
open FStar.String

// Implementation 
type variable_type = 
  | Var of string
type terminal_type = 
  | Term of string
type variables = list variable_type // (finite) set of variables
type terminals = list terminal_type // (finite) set of terminals
type rhs' = 
  | T of terminal_type
  | V of variable_type
type rhs_type = (ls: list rhs'{List.length ls >= 1})
type production_type = variable_type * rhs_type
type start = variable_type

type cfg_type = {
  variables: variables;
  terminals: terminals;
  productions: list production_type;
  start: start
}

type derivation_state = list rhs' * option variable_type * list rhs'

let cfg_a: cfg_type = {
  variables = [Var "A"];
  terminals = [Term "a"];
  productions = [
    (Var "A", [T (Term "a")]);
    (Var "A", [V (Var "A"); T (Term "a")])
  ];
  start = Var "A"
}

let move_everything_right (state: derivation_state) 
  : derivation_state
  = match state with 
    | (left, None, right) -> ([], None, List.append left right)
    | (left, Some var, right) -> ([], None, List.append left ((V var) :: right))

let is_middle_none (state: derivation_state)
  : bool 
  = match state with 
    | (_, None, _) -> true 
    | _ -> false

let get_right (state: derivation_state)
  : list rhs' 
  = match state with 
    | (_, _, right) -> right

let get_left (state: derivation_state)
  : list rhs' 
  = match state with 
    | (left, _, _) -> left

let rec all_variable_states (state: derivation_state{is_middle_none state}) (var: variable_type)
  : Tot (list derivation_state) (decreases get_right state)
  = match state with 
    | (left, None, []) -> []
    | (left, None, T t :: right') -> 
      all_variable_states (List.append left [T t], None, right') var
    | (left, None, V var' :: right') -> 
      if var' = var then (left, Some var, right') :: all_variable_states (List.append left [V var], None, right') var
      else all_variable_states (List.append left [V var'], None, right') var

let rec count_variable (ls: list rhs') (var: variable_type)
  : nat 
  = match ls with 
    | [] -> 0 
    | T _ :: ls' -> count_variable ls' var
    | V var' :: ls' -> count_variable ls' var + (if var' = var then 1 else 0)

let count_variable_state (state: derivation_state) (var: variable_type)
  : nat 
  = match state with 
    | (left, None, right) -> count_variable left var + count_variable right var
    | (left, Some var, right) -> 1 + count_variable left var + count_variable right var

let apply_production_rule (state: derivation_state) (production: production_type)
  : option derivation_state
  = let (var, rhs) = production in 
    match state with 
    | (left, None, right) -> None
    | (left, Some var', right) -> 
        if var' = var then Some (left, None, List.append rhs right)
        else None

let rec derivation_step (states: list derivation_state) (production: production_type)
  : Tot (list derivation_state) (decreases states)
  = match states with 
    | [] -> []
    | state :: states' -> 
      begin
        match apply_production_rule state production with 
        | None -> derivation_step states' production
        | Some state' -> state' :: derivation_step states' production
      end

let rec power_step (state: derivation_state) (productions: list production_type)
  : Tot (list derivation_state) (decreases productions)
  = match productions with
    | [] -> []
    | (var, rhs) :: productions' -> 
        let state_right = move_everything_right state in 
        let states = all_variable_states state_right var in
        List.append (derivation_step states (var, rhs)) (power_step state productions')

let rec power_step_list (states: list derivation_state) (productions: list production_type)
  : Tot (list derivation_state) (decreases states)
  = match states with 
    | [] -> []
    | state :: states' ->
      List.append (power_step state productions) (power_step_list states' productions)

let rec n_power_steps (states: list derivation_state) (productions: list production_type) (n: pos)
  : Tot (list derivation_state) (decreases n)
  = match n with 
    | 1 -> power_step_list states productions
    | _ -> n_power_steps (power_step_list states productions) productions (n - 1)

let n_power_steps_test_lemma _ 
  : Lemma (ensures 
            n_power_steps [([], Some (Var "A"), [])] cfg_a.productions 3 == [
                                                                              ([], None, [T (Term "a"); T (Term "a"); T (Term "a")]);
                                                                              ([], None, [V (Var "A"); T (Term "a"); T (Term "a"); T (Term "a")])
                                                                            ]
          )
  = normalize_term_spec (n_power_steps [([], Some (Var "A"), [])] cfg_a.productions 3)

let rec only_terminals (xs: list rhs')
  : bool 
  = match xs with 
    | [] -> true
    | T _ :: xs' -> only_terminals xs' 
    | V _ :: xs' -> false 

let is_word (state: derivation_state)
  : bool 
  = match state with 
    | (left, None, right) -> only_terminals left && only_terminals right
    | _ -> false

let word_in_language (word: derivation_state{is_word word}) (cfg: cfg_type) (n: pos)
  : bool 
  = List.contains word (n_power_steps [([], Some cfg.start, [])] cfg.productions n)

let word_in_language_test_lemma _ 
  : Lemma (ensures word_in_language ([], None, [T (Term "a"); T (Term "a"); T (Term "a")]) cfg_a 3)
  = normalize_term_spec (word_in_language ([], None, [T (Term "a"); T (Term "a"); T (Term "a")]) cfg_a 3)

// Transformation
let rec handle_rhs (rhs: rhs_type) (terminal_to_replace: terminal_type) (new_variable: variable_type)
  : (ls: rhs_type{List.length ls >= 1})
  = match rhs with
    | [T t] -> 
      if t = terminal_to_replace then [V new_variable]
      else [T t]
    | [V v] -> [V v]
    | T t :: rhs' -> 
      if t = terminal_to_replace then 
        V new_variable :: handle_rhs rhs' terminal_to_replace new_variable
      else 
        T t :: handle_rhs rhs' terminal_to_replace new_variable
    | V v :: rhs' -> 
      V v :: handle_rhs rhs' terminal_to_replace new_variable

let rec handle_productions (productions: list production_type) (terminal_to_replace: terminal_type) (new_variable: variable_type)
  : list production_type
  = match productions with 
    | [] -> []
    | (var, rhs) :: productions' -> 
      let new_rhs = handle_rhs rhs terminal_to_replace new_variable in 
      (var, new_rhs) :: handle_productions productions' terminal_to_replace new_variable

let handle_productions_test_lemma _ 
  : Lemma (ensures handle_productions cfg_a.productions (Term "a") (Var "C0") == [(Var "A", [V (Var "C0")]);
                                                                                  (Var "A", [V (Var "A"); V (Var "C0")])
                                                                                ]
          )
  = normalize_term_spec (handle_productions cfg_a.productions (Term "a") (Var "C0"))

let valid_substitution (cfg: cfg_type) (terminal_to_replace: terminal_type) (new_variable: variable_type)
  : bool 
  = List.contains terminal_to_replace cfg.terminals && 
    not (List.contains new_variable cfg.variables)

let remove_terminal_and_introduce_variable (cfg: cfg_type) (terminal_to_replace: terminal_type) (new_variable: variable_type)
  : cfg_type
  = let updated_productions = handle_productions cfg.productions terminal_to_replace new_variable in 
    { cfg with
        productions = (new_variable, [T terminal_to_replace]) :: updated_productions; 
        variables = new_variable :: cfg.variables }

let remove_terminal_and_introduce_variable_test_lemma _ 
  : Lemma (ensures 
            remove_terminal_and_introduce_variable cfg_a (Term "a") (Var "C0") == { 
                                                                                    variables = [Var "C0"; Var "A"];
                                                                                    terminals = [Term "a"];
                                                                                    productions = [
                                                                                      (Var "C0", [T (Term "a")]);
                                                                                      (Var "A", [V (Var "C0")]);
                                                                                      (Var "A", [V (Var "A"); V (Var "C0")]);
                                                                                    ];
                                                                                    start = Var "A"
                                                                                  }
          )
  = normalize_term_spec (remove_terminal_and_introduce_variable cfg_a (Term "a") (Var "C0"))

// Properties
let one_more_variable (cfg: cfg_type) (terminal_to_replace: terminal_type) (new_variable: variable_type)
  : Lemma (requires valid_substitution cfg terminal_to_replace new_variable)
          (ensures 
            List.length cfg.variables + 1 == 
            List.length (remove_terminal_and_introduce_variable cfg terminal_to_replace new_variable).variables
          )
  = ()

let simplify_word (state: derivation_state)
  : derivation_state
  = match state with 
    | (left, None, right) -> ([], None, List.append left right)
    | (left, Some var, right) -> ([], None, List.append left ((V var) :: right))

let original_is_in_new_general (word: derivation_state{is_word word}) (state: derivation_state) (cfg cfg': cfg_type) (terminal_to_replace: terminal_type) (new_variable: variable_type)
  : Lemma (requires 
            valid_substitution cfg terminal_to_replace new_variable /\
            cfg' == remove_terminal_and_introduce_variable cfg terminal_to_replace new_variable /\
            exists (n: pos). word_in_language word cfg n
          )
          (ensures 
            exists (n': pos). word_in_language word cfg' n'
          )
  = ()

let rec all_variable_states_length (state: derivation_state) (var: variable_type)
  : Lemma (ensures 
            List.length (all_variable_states (move_everything_right state) var)
            == count_variable_state state var
          )
  = match move_everything_right state with 
    | ([], None, right) -> ()