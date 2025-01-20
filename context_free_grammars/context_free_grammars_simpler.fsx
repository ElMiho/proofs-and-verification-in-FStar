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