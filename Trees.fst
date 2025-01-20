module Trees

type simple_binary_tree = 
  | SimpleBinaryLeaf of int
  | SimpleBinaryNode of simple_binary_tree * int * simple_binary_tree

let height (t: simple_binary_tree): int
  = match t with
    |