(** abstract tree representation *)

type atom = string
type variable = string


type logical_binop = And | Or | Implies | Equiv
type logical_unop = Not
type term_binop = Equal | NotEqual
type quantifier = Forall | Exist

type fmla =
  | FBinop of logical_binop * fmla * fmla
  | FUnop of logical_unop * fmla
  | FQuant of quantifier * variable list * fmla
  | FPred of predicate * term list
  | FTermBinop of term_binop * term * term
and term =
  | TAtom of atom
  | TVar of variable
  | TFunctor of atom * term list
and predicate = string


type decl = FOF of string * declType * fmla
and declType = Axiom | Conjecture

type tptp = decl list
