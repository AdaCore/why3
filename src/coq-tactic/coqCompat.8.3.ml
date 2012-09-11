

let body_of_constant c = c.Declarations.const_body

let on_leaf_node node f =
  match node with
  | Lib.Leaf lobj -> f lobj
  | Lib.CompilingLibrary _
  | Lib.OpenedModule _
  | Lib.ClosedModule  _
  | Lib.OpenedModtype _
  | Lib.ClosedModtype _
  | Lib.OpenedSection _
  | Lib.ClosedSection _
  | Lib.FrozenState _ -> ()
