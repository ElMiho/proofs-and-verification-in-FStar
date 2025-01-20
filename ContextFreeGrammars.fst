module ContextFreeGrammars

type variable = 
    | Var of string
type terminal = 
    | Term of string
type variables = variable list // (finite) set of variables
type terminals = terminal list // (finite) set of terminals
type rhs' = 
    | T of terminal
    | V of variable
type rhs = rhs' list
type production = variable * rhs
type start = variable

type cfg = {
    productions: int list
}