
type ident = Ptree.ident

type decl =
  | LogicDecl of Ptree.decl list

type file = decl list

