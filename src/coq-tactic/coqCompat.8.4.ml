
let body_of_constant = Declarations.body_of_constant

let on_leaf_node node f =
  match node with
  | Lib.Leaf lobj -> f lobj
  | Lib.CompilingLibrary _
  | Lib.OpenedModule _
  | Lib.ClosedModule  _
  | Lib.OpenedSection _
  | Lib.ClosedSection _
  | Lib.FrozenState _ -> ()
