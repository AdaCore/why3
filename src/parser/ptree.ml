(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(** {1 Parse trees}

The module provides datatypes for WhyML parse trees.

These datatypes are produced by the WhyML parser module [Parser].

They can be alternatively produced via OCaml code, and processed later
   on by typing module [Typing]. See also Section 4.9. "ML Programs"
   of the documentation.

*)

open Mysexplib.Std [@@warning "-33"]

(** {2 Identifiers and attributes} *)

(** attributes, with a specific case for a source location *)
type attr =
  | ATstr of Ident.attribute
  | ATpos of Loc.position
[@@deriving sexp]

(** identifiers, with attributes and a source location *)
type ident = {
  id_str : string;
  id_ats : attr list;
  id_loc : Loc.position;
}
[@@deriving sexp]

(** qualified identifiers *)
type qualid =
  | Qident of ident
  | Qdot of qualid * ident
[@@deriving sexp]

(** {2 Types} *)

(** type expressions *)
type pty =
  | PTtyvar of ident
  (** type variable *)
  | PTtyapp of qualid * pty list
  (** type constructor, possibly with arguments, e.g., [int], [list bool], etc. *)
  | PTtuple of pty list
  (** tuples, e.g., [(int,bool)] *)
  | PTref   of pty list
  (** reference type, e.g., [ref int], as used by the "auto-dereference"
     mechanism (See manual Section 13.1. "Release Notes for version
     1.2: new syntax for auto-dereference") *)
  | PTarrow of pty * pty
  (** arrow type, e.g., [int -> bool] *)
  | PTscope of qualid * pty
  (** opening scope locally, e.g., [M.((list t,u))] *)
  | PTparen of pty
  (** parenthesised type *)
  | PTpure  of pty
  (** purify a type *)
[@@deriving sexp]


(** {2 Patterns} *)

(** "ghost" modifier *)
type ghost = bool
[@@deriving sexp]

(** Patterns, equipped with a source location *)
type pattern = {
  pat_desc : pat_desc;
  pat_loc  : Loc.position;
}

and pat_desc =
  | Pwild
  (** wildcard, that is "_" *)
  | Pvar of ident
  (** variable as a pattern *)
  | Papp of qualid * pattern list
  (** constructor pattern, e.g., [Cons(x,y)] *)
  | Prec of (qualid * pattern) list
  (** record pattern *)
  | Ptuple of pattern list
  (** tuple pattern *)
  | Pas of pattern * ident * ghost
  (** as-pattern, e.g., [Cons(x,y) as z] *)
  | Por of pattern * pattern
  (** or-pattern [p1 | p2] *)
  | Pcast of pattern * pty
  (** type cast *)
  | Pscope of qualid * pattern
  (** open scope locally *)
  | Pparen of pattern
  (** parenthesised pattern *)
  | Pghost of pattern
  (** explicitly ghost pattern *)
[@@deriving sexp]


(** {2 Logical terms and formulas} *)

(** binder as 4-uple [(loc,id,ghost,type)] to represent "ghost? id? :
   type?". [id] and [type] cannot be [None] at the same time *)
type binder = Loc.position * ident option * ghost * pty option
[@@deriving sexp]

(** parameter as 4-uple [(loc,id,ghost,type)] to represent
   "ghost? id? : type". *)
type param  = Loc.position * ident option * ghost * pty
[@@deriving sexp]

(** Terms, equipped with a source location *)
type term = {
  term_desc : term_desc;
  term_loc  : Loc.position;
}

and term_desc =
  | Ttrue
  (** the true proposition *)
  | Tfalse
  (** the false proposition *)
  | Tconst of Constant.constant
  (** constant literals *)
  | Tident of qualid
  (** identifiers *)
  | Tasref of qualid
  (** identifier as reference, e.g., [&x] (See manual Section
     13.1. "Release Notes for version 1.2: new syntax for
     auto-dereference") *)
  | Tidapp of qualid * term list
  (** (first-order) application of a logic identifier to a list of terms *)
  | Tapply of term * term
  (** curried application, of a term to a term *)
  | Tinfix of term * ident * term
  (** application of a binary operation in an infix fashion, allowing chaining.
      For example, [Tinfix(t1,"<=",Tinfix(t2,"<",t3))] denotes
      [t1 <= t2 /\ t2 < t3] *)
  | Tinnfix of term * ident * term
  (** application of a binary operation in an infix style, but without chaining *)
  | Tbinop of term * Dterm.dbinop * term
  (** application of a binary logic connective, in an infix fashion, allowing
      chaining. For example, [Tbinop(p1,"<->",Tbinop(p2,"<->",p3))] denotes
      [(p1 <-> p2) /\ (p2 <-> p3)] *)
  | Tbinnop of term * Dterm.dbinop * term
  (** application of a binary logic connective, but without chaining *)
  | Tnot of term
  (** logic negation *)
  | Tif of term * term * term
  (** if-expression *)
  | Tquant of Dterm.dquant * binder list * term list list * term
  (** quantified formulas. The third argument is a list of triggers. *)
  | Teps of ident * pty * term
  (** [Teps(x,ty,f)] denotes the epsilon term "any [x] of type [ty]
     that satisfies [f]".  Use with caution since if there is no such
     [x] satisfying [f], then it acts like introducing an inconsistent
     axiom. (As a matter of fact, this is the reason why there is no
     concrete syntax for such epsilon-terms.) *)
  | Tattr of attr * term
  (** term annotated with an attribute *)
  | Tlet of ident * term * term
  (** let-expression *)
  | Tcase of term * (pattern * term) list
  (** pattern-matching *)
  | Tcast of term * pty
  (** type casting *)
  | Ttuple of term list
  (** tuples *)
  | Trecord of (qualid * term) list
  (** record expressions *)
  | Tupdate of term * (qualid * term) list
  (** record update expression *)
  | Tscope of qualid * term
  (** local scope *)
  | Tat of term * ident
  (** "at" modifier. The "old" modifier is a particular case with
     the identifier [Dexpr.old_label]  *)

[@@deriving sexp]

(** {2 Program expressions} *)

(** Loop invariant or type invariant *)
type invariant = term list
[@@deriving sexp]

(** Variant for both loops and recursive functions. The option
   identifier is an optional ordering predicate *)
type variant = (term * qualid option) list
[@@deriving sexp]

(** Precondition *)
type pre = term
[@@deriving sexp]

(** Normal postconditions *)
type post = Loc.position * (pattern * term) list
[@@deriving sexp]

(** Exceptional postconditions *)
type xpost = Loc.position * (qualid * (pattern * term) option) list
[@@deriving sexp]

(** Contract *)
type spec = {
    sp_pre     : pre list; (** preconditions *)
    sp_post    : post list; (** normal postconditions *)
    sp_xpost   : xpost list; (** exceptional postconditions *)
    sp_reads   : qualid list; (** "reads" clause *)
    sp_writes  : term list;   (** "writes" clause *)
    sp_alias   : (term * term) list; (** "alias" clause *)
    sp_variant : variant; (** variant for recursive functions *)
    sp_checkrw : bool; (** should the reads and writes clauses be checked against the given body? *)
    sp_diverge : bool; (** may the function diverge? *)
    sp_partial : bool; (** is the function partial? *)
}
[@@deriving sexp]

(** Expressions, equipped with a source location *)
type expr = {
    expr_desc : expr_desc;
    expr_loc  : Loc.position;
  }

(** Expression kinds *)
and expr_desc =
  | Eref
  (** built-in operator [ref] for auto-dereference syntax. (See manual Section
     13.1. "Release Notes for version 1.2: new syntax for
     auto-dereference")  *)
  | Etrue
  (** Boolean literal [True] *)
  | Efalse
  (** Boolean literal [False] *)
  | Econst of Constant.constant
  (** Constant literals *)
  | Eident of qualid
  (** Variable identifier *)
  | Easref of qualid
  (** identifier as reference, e.g., [&x]  (See manual Section
     13.1. "Release Notes for version 1.2: new syntax for
     auto-dereference")  *)
  | Eidapp of qualid * expr list
  (** Uncurried application of a function identifier to a list of arguments *)
  | Eapply of expr * expr
  (** Curried application *)
  | Einfix of expr * ident * expr
  (** application of a binary function identifier, in an infix fashion, allowing
     chaining, e.g., [Einfix(e1,"<=",Einfix(e2,"<",e3))] denotes
     [e1 <= e2 && e2 < e3] *)
  | Einnfix of expr * ident * expr
  (** application of a binary function, but without chaining *)
  | Elet of ident * ghost * Expr.rs_kind * expr * expr
  (** [let ... in ...] expression *)
  | Erec of fundef list * expr
  (** Local definition of function(s), possibly mutually recursive *)
  | Efun of binder list * pty option * pattern * Ity.mask * spec * expr
  (** Anonymous function *)
  | Eany of param list * Expr.rs_kind * pty option * pattern * Ity.mask * spec
  (** "any params : ty <spec>": abstract expression with a specification,
       generating a VC for existence *)
  | Etuple of expr list
  (** Tuple of expressions *)
  | Erecord of (qualid * expr) list
  (** Record expression, e.g., [{f=e1; g=e2; ...}] *)
  | Eupdate of expr * (qualid * expr) list
  (** Record update, e.g., [{e with f=e1; ...}] *)
  | Eassign of (expr * qualid option * expr) list
  (** Assignment, of a mutable variable (no qualid given) or of a record field (qualid
      given). Assignments are possibly in parallel, e.g., [x.f, y.g, z <- e1, e2, e3] *)
  | Esequence of expr * expr
  (** Sequence of two expressions, the first one being supposed of type unit *)
  | Eif of expr * expr * expr
  (** [if e1 then e2 else e3] expression *)
  | Ewhile of expr * invariant * variant * expr
  (** [while] loop with annotations *)
  | Eand of expr * expr
  (** lazy conjunction *)
  | Eor of expr * expr
  (** lazy disjunction *)
  | Enot of expr
  (** Boolean negation *)
  | Ematch of expr * reg_branch list * exn_branch list
  (** match expression, including both regular patterns and exception
     patterns (those lists cannot be both empty) *)
  | Eabsurd
  (** [absurd] statement to mark unreachable branches *)
  | Epure of term
  (** turns a logical term into a pure expression, e.g., [pure { t }] *)
  | Eidpur of qualid
  (** promotes a logic symbol in programs, e.g., [{f}] or [M.{f}] *)
  | Eraise of qualid * expr option
  (** raise an exception, possibly with an argument *)
  | Eexn of ident * pty * Ity.mask * expr
  (** local declaration of an exception, e.g., [let exception E in e] *)
  | Eoptexn of ident * Ity.mask * expr
  (** local declaration of an exception, implicitly captured. Used by Why3 for handling
      [return], [break], and [continue] *)
  | Efor of ident * expr * Expr.for_direction * expr * invariant * expr
  (** "for" loops *)
  | Eassert of Expr.assertion_kind * term
  (** [assert], [assume], and [check] expressions *)
  | Escope of qualid * expr
  (** open scope locally, e.g., [M.(e)] *)
  | Elabel of ident * expr
  (** introduction of a label, e.g., [label L in e] *)
  | Ecast of expr * pty
  (** cast an expression to a given type, e.g., [(e:ty)] *)
  | Eghost of expr
  (** forces an expression to be ghost, e.g., [ghost e] *)
  | Eattr of attr * expr
  (** attach an attribute to an expression *)

(** A regular match branch *)
and reg_branch = pattern * expr

(** An exception match branch *)
and exn_branch = qualid * pattern option * expr

(** Local function definition *)
and fundef = ident * ghost * Expr.rs_kind *
               binder list * pty option * pattern * Ity.mask * spec * expr
[@@deriving sexp]

(** {2 Declarations} *)

(** record fields *)
type field = {
  f_loc     : Loc.position;
  f_ident   : ident;
  f_pty     : pty;
  f_mutable : bool;
  f_ghost   : bool
}
[@@deriving sexp]

(** Type definition body *)
type type_def =
  | TDalias     of pty
  (** alias type *)
  | TDalgebraic of (Loc.position * ident * param list) list
  (** algebraic type *)
  | TDrecord    of field list
  (** record type *)
  | TDrange     of BigInt.t * BigInt.t
  (** integer type in given range  *)
  | TDfloat     of int * int
  (** floating-point type with given exponent and precision *)
[@@deriving sexp]

(** The different kinds of visibility *)
type visibility = Public | Private | Abstract (** = Private + ghost fields *)
[@@deriving sexp]

(** A type declaration *)
type type_decl = {
  td_loc    : Loc.position;
  td_ident  : ident;
  td_params : ident list;
  td_vis    : visibility; (** visibility, for records only *)
  td_mut    : bool;       (** mutability, for records or abstract types *)
  td_inv    : invariant;  (** invariant, for records only *)
  td_wit    : expr option;  (** witness for the invariant *)
  td_def    : type_def;
}
[@@deriving sexp]

(** A single declaration of a function or predicate *)
type logic_decl = {
  ld_loc    : Loc.position;
  ld_ident  : ident;
  ld_params : param list;
  ld_type   : pty option;
  ld_def    : term option;
}
[@@deriving sexp]

(** A single declaration of an inductive predicate *)
type ind_decl = {
  in_loc    : Loc.position;
  in_ident  : ident;
  in_params : param list;
  in_def    : (Loc.position * ident * term) list;
}
[@@deriving sexp]

(** Arguments of "meta" declarations *)
type metarg =
  | Mty  of pty
  | Mfs  of qualid
  | Mps  of qualid
  | Max  of qualid
  | Mlm  of qualid
  | Mgl  of qualid
  | Mval of qualid
  | Mstr of string
  | Mint of int
[@@deriving sexp]

(** The possible "clone" substitution elements *)
type clone_subst =
  | CStsym  of qualid * ident list * pty
  | CSfsym  of qualid * qualid
  | CSpsym  of qualid * qualid
  | CSvsym  of qualid * qualid
  | CSxsym  of qualid * qualid
  | CSprop  of Decl.prop_kind
  | CSaxiom of qualid
  | CSlemma of qualid
  | CSgoal  of qualid
[@@deriving sexp]

(** top-level declarations *)
type decl =
  | Dtype of type_decl list
  (** Type declaration *)
  | Dlogic of logic_decl list
  (** Collection of "function"s and "predicate"s, mutually recursively declared *)
  | Dind of Decl.ind_sign * ind_decl list
  (** An inductive or co-inductive predicate *)
  | Dprop of Decl.prop_kind * ident * term
  (** Propositions: "lemma" or "goal" or "axiom" *)
  | Dlet of ident * ghost * Expr.rs_kind * expr
  (** Global program variable or function *)
  | Drec of fundef list
  (** set of program functions, defined mutually recursively *)
  | Dexn of ident * pty * Ity.mask
  (** Declaration of global exceptions *)
  | Dmeta of ident * metarg list
  (** Declaration of a "meta" *)
  | Dcloneexport of Loc.position * qualid * clone_subst list
  (** "clone export" *)
  | Duseexport of Loc.position * qualid
  (** "use export" *)
  | Dcloneimport of Loc.position * bool * qualid * ident option * clone_subst list
  (** "clone import ... as ..." *)
  | Duseimport of Loc.position * bool * (qualid * ident option) list
  (** "use import ... as ..." *)
  | Dimport of qualid
  (** "import" *)
  | Dscope of Loc.position * bool * ident * decl list
  (** "scope" *)
[@@deriving sexp]

let sexp_of_mlw_file _ = assert false [@@warning "-32"]
let mlw_file_of_sexp _ = assert false  [@@warning "-32"]
(* default values if the line below does not produce anything, i.e.,
   when ppx_sexp_conv is not installed *)

type mlw_file =
  | Modules of (ident * decl list) list
  (** a list of modules containing lists of declarations *)
  | Decls of decl list
  (** a list of declarations outside any module *)
[@@deriving sexp]
