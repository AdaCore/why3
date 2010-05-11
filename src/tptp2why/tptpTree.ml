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
  | TConst of string
  | TVar of variable
  | TFunctor of atom * term list
and predicate = string


(** a tptp declaration *)
type decl =
| Fof of string * declType * fmla
| Cnf of string * declType * fmla
| Include of string
and declType = Axiom | Conjecture | NegatedConjecture | Lemma

type tptp = decl list
