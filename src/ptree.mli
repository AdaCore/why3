
(*s Parse trees. *)

type loc = Loc.position

(*s Logical expressions (for both terms and predicates) *)

type real_constant = 
  | RConstDecimal of string * string * string option (* int / frac / exp *)
  | RConstHexa of string * string * string

type constant =
  | ConstInt of string
  | ConstFloat of real_constant

type pp_infix = 
  PPand | PPor | PPimplies | PPiff |
  PPlt | PPle | PPgt | PPge | PPeq | PPneq |
  PPadd | PPsub | PPmul | PPdiv | PPmod

type pp_prefix = 
  PPneg | PPnot

type ppure_type =
  | PPTint
  | PPTbool
  | PPTreal
  | PPTunit
  | PPTvarid of string * Loc.position
  | PPTexternal of ppure_type list * string * Loc.position

type lexpr = 
  { pp_loc : loc; pp_desc : pp_desc }

and pp_desc =
  | PPvar of string
  | PPapp of string * lexpr list
  | PPtrue
  | PPfalse
  | PPconst of constant
  | PPinfix of lexpr * pp_infix * lexpr
  | PPprefix of pp_prefix * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPforall of string * ppure_type * lexpr list list * lexpr
  | PPexists of string * ppure_type * lexpr
  | PPnamed of string * lexpr
  | PPlet of string * lexpr * lexpr
  | PPmatch of lexpr * ((string * string list * loc) * lexpr) list

(*s Declarations. *)

type external_ = bool

type plogic_type =
  | PPredicate of ppure_type list
  | PFunction of ppure_type list * ppure_type

type decl = 
  | Logic of loc * external_ * string list * plogic_type
  | Predicate_def of loc * string * (loc * string * ppure_type) list * lexpr
  | Inductive_def of loc * string * plogic_type * (loc * string * lexpr) list
  | Function_def 
      of loc * string * (loc * string * ppure_type) list * ppure_type * lexpr
  | Axiom of loc * string * lexpr
  | Goal of loc * string * lexpr
  | TypeDecl of loc * external_ * string list * string
  | AlgType of (loc * string list * string
      * (loc * string * ppure_type list) list) list

type file = decl list
