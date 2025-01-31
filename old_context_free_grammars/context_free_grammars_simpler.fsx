type Variable = 
    | Var of string
type Terminal = 
    | Term of string
type Variables = Variable list // (finite) set of variables
type Terminals = Terminal list // (finite) set of terminals
type RHS' = 
    | T of Terminal
    | V of Variable
type RHS = RHS' list
type Production = Variable * RHS
type Start = Variable

type CFG = {
    variables: Variables;
    terminals: Terminals;
    productions: Production list;
    start: Start
}

let A_CFG: CFG = {
    variables = [Var "A"];
    terminals = [Term "a"; Term "+"];
    productions = [
        (Var "A", [T (Term "a")]);
        (Var "A", [V (Var "A"); T (Term "+"); V (Var "A")])
    ];
    start = Var "A"
}

let A_CFG': CFG = {
    variables = [Var "A"; Var "B"];
    terminals = [Term "a"; Term "+"];
    productions = [
        (Var "A", [T (Term "a")]);
        (Var "A", [V (Var "A"); T (Term "+"); V (Var "A")]);
        (Var "B", [T (Term "+"); V (Var "A")])
    ];
    start = Var "A"
}

let sound_CFG (cfg: CFG): bool = 
    cfg.variables <> [] && cfg.terminals <> [] && // Non-empty variables and terminals
    List.contains cfg.start cfg.variables && // Start is included
    // Production rules makes sense
    List.forall (
        fun (var, rhs) -> 
            List.contains var cfg.variables &&
            List.forall (
                fun exp -> 
                    match exp with
                    | V v -> List.contains v cfg.variables
                    | T t -> List.contains t cfg.terminals
            ) rhs
    ) cfg.productions

// construction for (a)
let handle_one_production_a ((var, rhs): Production) count = 
    if List.length rhs >= 2 then
        let (res', count', new_productions) = List.foldBack (
            fun p (acc, c, prods) -> 
                match p with
                | V v -> 
                    V v :: acc, c, prods
                | T t -> 
                    let newVar = Var ("Z" + string c)
                    V newVar :: acc, c + 1, (newVar, [T t]) :: prods) rhs ([], count, [])
        (var, res') :: new_productions, count'
    else [(var, rhs)], count

// handle_one_production_a (Var "A", [V (Var "A"); T (Term "+"); V (Var "A")]) 0

let rec handle_all_productions_a productions count = 
    match productions with
    | [] -> [], count
    | (var, rhs) :: productions' -> 
        let (new_productions, count') = handle_one_production_a (var, rhs) count
        let (res, count'') = handle_all_productions_a productions' count'
        new_productions @ res, count''

// handle_all_productions_a [(Var "A", [T (Term "a")]); (Var "A", [V (Var "A"); T (Term "+"); V (Var "A")])] 0
// handle_all_productions_a [(Var "A", [T (Term "a")]); (Var "A", [V (Var "A"); T (Term "+"); V (Var "A")]); (Var "B", [T (Term "+"); V (Var "A")])] 0

// Does *not* return a vaild CFG at the moment
let construction_a (cfg: CFG) = 
    let (new_productions, _) = handle_all_productions_a cfg.productions 0
    { cfg with productions = new_productions }

// construction for (b)
let rec handle_one_production_b ((var, rhs): Production) (count: int): Production list * int = 
    match rhs with
    | [] -> [], count
    | [T t] -> [(var, [T t])], count
    | [x; y] -> [(var, [x; y])], count
    | v :: rhs' -> 
        let CVar = Var ("C" + string count)
        let (res, count') = handle_one_production_b (CVar, rhs') (count + 1)
        (var, [v; V CVar]) :: res, count'

// handle_one_production_b (Var "A", [V (Var "A"); V (Var "Z0"); V (Var "A")]) 0;;

let rec handle_all_productions_b (productions: Production list) (count: int): Production list * int = 
    match productions with
    | [] -> [], count
    | (var, rhs) :: productions' -> 
        if List.length rhs >= 2 then
            let (new_productions, count') = handle_one_production_b (var, rhs) count
            let (new_productions', count'') = handle_all_productions_b productions' count'
            new_productions @ new_productions', count''
        else 
            let (new_productions', count'') = handle_all_productions_b productions' count
            (var, rhs) :: new_productions', count''

let construction_b (cfg: CFG) = 
    let (updated_productions, _) = handle_all_productions_b cfg.productions 0
    { cfg with productions = updated_productions }

let entire_construction (cfg: CFG) = 
    let cfg' = construction_b (construction_a cfg)
    let updated_variables = List.map (fun (var, _) -> var) cfg'.productions
    { cfg' with variables = updated_variables }

let bigger_CFG = {
    variables = [Var "A"; Var "B"];
    terminals = [Term "a"; Term "b"; Term "c"];
    productions = [
        (Var "A", [T (Term "a")]);
        (Var "A", [V (Var "A"); T (Term "+"); V (Var "B")]);
        (Var "B", [T (Term "b")]);
        (Var "B", [V (Var "B"); V (Var "A"); T (Term "a")])
    ]
    start = Var "A"
}
let bigger_CFG_CNF = entire_construction bigger_CFG

// Abstract syntax tree
type AST = 
    | Node of Variable * AST list
    | T' of Terminal

// A -> a | A + A with a+a+a
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

// same string as above but with grammar in CNF
let A_CFG_CNF = construction_b (construction_a A_CFG)
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

let illegal = 
    Node (Var "A", [
        Node (Var "A", [T' (Term "a")]);
        T' (Term "K");
        Node (Var "A", [T' (Term "a")])
    ])

let rec print_AST (ast: AST): string = 
    match ast with
    | Node (var, ast_list) -> print_AST_list ast_list
    | T' (Term t) -> t
and print_AST_list (ast_list: AST list): string = 
    match ast_list with
    | [] -> ""
    | ast :: ast_list' -> 
        print_AST ast + print_AST_list ast_list'

let rec get_production_rhs_from_AST (ast_list: AST list) = 
    match ast_list with
    | [] -> []
    | Node (var, _) :: ast_list' -> V var :: get_production_rhs_from_AST ast_list'
    | T' term :: ast_list' -> T term :: get_production_rhs_from_AST ast_list'

let rec AST_in_CFG (ast: AST) (cfg: CFG): bool =
    match ast with
    | Node (var, ast_list) -> 
        let rhs = get_production_rhs_from_AST ast_list
        List.contains var cfg.variables && List.contains (var, rhs) cfg.productions &&
        AST_in_CFG_list ast_list cfg
    | T' t -> 
        true // valid since we use get_production_rhs_from_AST and checks above if it is a production rule
and AST_in_CFG_list (ast_list: AST list) (cfg: CFG): bool = 
    match ast_list with
    | [] -> true
    | ast :: ast_list' -> AST_in_CFG ast cfg && AST_in_CFG_list ast_list' cfg

// AST_in_CFG aPaPa A_CFG

let rec get_vars_from_productions (productions: Production list) = 
    match productions with
    | [] -> []
    | (var, _) :: productions' -> var :: get_vars_from_productions productions'

let rec convert_AST_CNF_to_AST (ast_CNF: AST) (cfg: CFG) = 
    match ast_CNF with 
    | Node (var, ast_CNF_list) -> 
        if List.contains var cfg.variables then 
            [Node (var, convert_AST_CNF_to_AST_list ast_CNF_list cfg)]
        else
            convert_AST_CNF_to_AST_list ast_CNF_list cfg
    | T' t -> [T' t]
and convert_AST_CNF_to_AST_list (ast_CNF_list: AST list) (cfg: CFG) = 
    match ast_CNF_list with
    | [] -> []
    | ast :: ast_CNF_list' -> 
        convert_AST_CNF_to_AST ast cfg @ convert_AST_CNF_to_AST_list ast_CNF_list' cfg

// let aPaPa' = List.head (convert_AST_CNF_to_AST aPaPa_CNF A_CFG)

let A_CFG_other = {
    variables = [Var "A"];
    terminals = [Term "a"; Term "+"];
    productions = [
        (Var "A", [T (Term "a")]);
        (Var "A", [T (Term "a"); T (Term "+"); V (Var "A")])
    ];
    start = Var "A"
}

let A_CFG_other_CNF = entire_construction A_CFG_other

let aPaPa_other = 
    Node (Var "A", [
        T' (Term "a");
        T' (Term "+");
        Node (Var "A", [
            T' (Term "a");
            T' (Term "+");
            Node (Var "A", [T' (Term "a")])
        ])
    ])

let aPaPa_other_CNF = 
    Node (Var "A", [
        Node (Var "Z1", [T' (Term "a")]);
        Node (Var "C0", [
            Node (Var "Z0", [T' (Term "+")]);
            Node (Var "A", [
                Node (Var "Z1", [T' (Term "a")]);
                Node (Var "C0", [
                    Node (Var "Z0", [T' (Term "+")]);
                    Node (Var "A", [T' (Term "a")])
                ])
            ])
        ])
    ])

let rec length_word_derivation (ast: AST) =
    match ast with 
    | Node (_, []) -> 1
    | Node (_, ast' :: ast_list) -> 1 + max (length_word_derivation ast') (length_word_derivation_list ast_list)
    | T' _ -> 1
and length_word_derivation_list (ast_list: AST list) = 
    match ast_list with
    | [] -> 0
    | ast :: ast_list' -> max (length_word_derivation ast) (length_word_derivation_list ast_list')

// To be continued if time permits it
// Idea: variable names does not matter; only structure and terminals (both value and position)
let rec same_structure (ast: AST) (ast_CNF: AST): bool = 
    match ast, ast_CNF with
    | Node (_, ast_list), Node (_, ast_CNF_list) -> same_structure_list ast_list ast_CNF_list
    | T' t1, T' t2 -> t1 = t2
    | _, _ -> false
and same_structure_list (ast_list: AST list) (ast_CNF_list: AST list): bool = 
    match ast_list, ast_CNF_list with
    | [], [] -> true
    | ast :: ast_list', ast_CNF :: ast_CNF_list' -> same_structure ast ast_CNF && same_structure_list ast_list' ast_CNF_list'
    | _, _ -> false

let tree1 = 
    Node (Var "A", [T' (Term "a")])
let tree2 = 
    Node (Var "B", [T' (Term "a")])
same_structure tree1 tree2

let rec convert_AST_to_AST_CNF (ast: AST) = 
    match ast with
    | T' t -> T' t
    | Node (Var s, T' t :: ast') -> 
and convert_AST_to_AST_CNF_list (ast_list: AST list) = 
    match ast_list with 
    | [] -> []