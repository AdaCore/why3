(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2020   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Mysexplib.Std [@@warning "-33"]

(** Parse trees *)

(** {1 Parse trees} *)

(** {2 Identifiers and attributes} *)

type attr =
  | ATstr of Ident.attribute
  | ATpos of Loc.position
[@@deriving sexp_of]

type ident = {
  id_str : string;
  id_ats : attr list;
  id_loc : Loc.position;
}
[@@deriving sexp_of]

type qualid =
  | Qident of ident
  | Qdot of qualid * ident
[@@deriving sexp_of]

(** {2 Types} *)

type pty =
  | PTtyvar of ident
  | PTtyapp of qualid * pty list
  | PTtuple of pty list
  | PTref   of pty list
  | PTarrow of pty * pty
  | PTscope of qualid * pty
  | PTparen of pty
  | PTpure  of pty
[@@deriving sexp_of]

(** {2 Patterns} *)

type ghost = bool
[@@deriving sexp_of]

type pattern = {
  pat_desc : pat_desc;
  pat_loc  : Loc.position;
}

and pat_desc =
  | Pwild
  | Pvar of ident
  | Papp of qualid * pattern list
  | Prec of (qualid * pattern) list
  | Ptuple of pattern list
  | Pas of pattern * ident * ghost
  | Por of pattern * pattern
  | Pcast of pattern * pty
  | Pscope of qualid * pattern
  | Pparen of pattern
  | Pghost of pattern
[@@deriving sexp_of]

(** {2 Logical terms and formulas} *)

type binder = Loc.position * ident option * ghost * pty option
[@@deriving sexp_of]

type param  = Loc.position * ident option * ghost * pty
[@@deriving sexp_of]

type term = {
  term_desc : term_desc;
  term_loc  : Loc.position;
}

and term_desc =
  | Ttrue
  | Tfalse
  | Tconst of Constant.constant
  | Tident of qualid
  | Tasref of qualid
  | Tidapp of qualid * term list
  | Tapply of term * term
  | Tinfix of term * ident * term
  | Tinnfix of term * ident * term
  | Tbinop of term * Dterm.dbinop * term
  | Tbinnop of term * Dterm.dbinop * term
  | Tnot of term
  | Tif of term * term * term
  | Tquant of Dterm.dquant * binder list * term list list * term
  | Tattr of attr * term
  | Tlet of ident * term * term
  | Tcase of term * (pattern * term) list
  | Tcast of term * pty
  | Ttuple of term list
  | Trecord of (qualid * term) list
  | Tupdate of term * (qualid * term) list
  | Tscope of qualid * term
  | Tat of term * ident
[@@deriving sexp_of]

(** {2 Program expressions} *)

(** Loop invariant or type invariant *)
type invariant = term list
[@@deriving sexp_of]

(** Variant for both loops and recursive functions *)
type variant = (term * qualid option) list
[@@deriving sexp_of]

(** Precondition *)
type pre = term
[@@deriving sexp_of]

(** Normal postcondition *)
type post = Loc.position * (pattern * term) list
[@@deriving sexp_of]

(** Exceptional postcondition *)
type xpost = Loc.position * (qualid * (pattern * term) option) list
[@@deriving sexp_of]

(** Contract *)
type spec = {
    sp_pre     : pre list; (** preconditions *)
    sp_post    : post list; (** normal postconditions *)
    sp_xpost   : xpost list; (** exceptional postconditions *)
    sp_reads   : qualid list; (** [reads] clause *)
    sp_writes  : term list;   (** [writes] clause *)
    sp_alias   : (term * term) list; (** [alias] clause *)
    sp_variant : variant; (** variant for recursive functions *)
    sp_checkrw : bool; (** should the reads and writes clauses be checked against the given body? *)
    sp_diverge : bool; (** may the function diverge? *)
    sp_partial : bool; (** is the function partial? *)
}
[@@deriving sexp_of]

(** Expressions, equipped with a source location *)
type expr = {
    expr_desc : expr_desc;
    expr_loc  : Loc.position;
  }

(** Expression kinds *)
and expr_desc =
  | Eref
  (** TODO: document *)
  | Etrue
  (** Boolean literal [True] *)
  | Efalse
  (** Boolean literal [False] *)
  | Econst of Constant.constant
  (** Constant literals *)
  | Eident of qualid
  (** Variable identifier *)
  | Easref of qualid
  (** TODO: document *)
  | Eidapp of qualid * expr list
  (** Uncurried application of a function identifier to a list of arguments *)
  | Eapply of expr * expr
  (** Curried application *)
  | Einfix of expr * ident * expr
  (** Infix operation *)
  | Einnfix of expr * ident * expr
  (** Infix operation (TODO: document the difference with the former) *)
  | Elet of ident * ghost * Expr.rs_kind * expr * expr
  (** [let ... in ...] expression *)
  | Erec of fundef list * expr
  (** Local definition of function, possibly mutually recursive *)
  | Efun of binder list * pty option * pattern * Ity.mask * spec * expr
  (** Anonymous function *)
  | Eany of param list * Expr.rs_kind * pty option * pattern * Ity.mask * spec
  (** [any]: abstract expression with a specification,
       generating of VC for existence *)
  | Etuple of expr list
  (** Tuple of expressions *)
  | Erecord of (qualid * expr) list
  (** Record expressions *)
  | Eupdate of expr * (qualid * expr) list
  (** Record update [{e with f=e1; ...}] *)
  | Eassign of (expr * qualid option * expr) list
  (** Parallel assignment ? TODO: document *)
  | Esequence of expr * expr
  (** Sequence of two expressions *)
  | Eif of expr * expr * expr
  (** [if .. then .. else ..] expression *)
  | Ewhile of expr * invariant * variant * expr
  (** [while] loop *)
  | Eand of expr * expr
  (** lazy conjunction *)
  | Eor of expr * expr
  (** lazy disjunction *)
  | Enot of expr
  (** negation *)
  | Ematch of expr * reg_branch list * exn_branch list
  (** match expression, including both regular patterns and exception
     patterns (those lists cannot be both empty) *)
  | Eabsurd
  (** [absurd] statement to mark unreachable branches *)
  | Epure of term
  (** turns a logical term into a pure expression *)
  | Eidpur of qualid
  (** TODO: document *)
  | Eraise of qualid * expr option
  (** raise an exception *)
  | Eexn of ident * pty * Ity.mask * expr
  (** local declaration of an exception *)
  | Eoptexn of ident * Ity.mask * expr
  (** TODO: document *)
  | Efor of ident * expr * Expr.for_direction * expr * invariant * expr
  (** [for] loop *)
  | Eassert of Expr.assertion_kind * term
  (** [assert] expression *)
  | Escope of qualid * expr
  (** TODO: document *)
  | Elabel of ident * expr
  (** introduction of a label *)
  | Ecast of expr * pty
  (** cast an expression to a given type *)
  | Eghost of expr
  (** forces an expression to be ghost *)
  | Eattr of attr * expr
  (** attach an attribute to an expression *)

(** A regular match branch *)
and reg_branch = pattern * expr

(** An exception match branch *)
and exn_branch = qualid * pattern option * expr

(** Local function definition *)
and fundef = ident * ghost * Expr.rs_kind *
               binder list * pty option * pattern * Ity.mask * spec * expr
[@@deriving sexp_of]

(** {2 Declarations} *)

(** record fields *)
type field = {
  f_loc     : Loc.position;
  f_ident   : ident;
  f_pty     : pty;
  f_mutable : bool;
  f_ghost   : bool
}
[@@deriving sexp_of]

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
[@@deriving sexp_of]

(** The different kinds of visibility *)
type visibility = Public | Private | Abstract (** = Private + ghost fields *)
[@@deriving sexp_of]

(** A type declaration *)
type type_decl = {
  td_loc    : Loc.position;
  td_ident  : ident;
  td_params : ident list;
  td_vis    : visibility; (** visibility, for records only *)
  td_mut    : bool;       (** mutability, for records or abstract types *)
  td_inv    : invariant;  (** invariant, for records only *)
  td_wit    : (qualid * expr) list;  (** witness for the invariant *)
  td_def    : type_def;
}
[@@deriving sexp_of]

(** A single declaration of a function or predicate *)
type logic_decl = {
  ld_loc    : Loc.position;
  ld_ident  : ident;
  ld_params : param list;
  ld_type   : pty option;
  ld_def    : term option;
}
[@@deriving sexp_of]

(** A single declaration of an inductive predicate *)
type ind_decl = {
  in_loc    : Loc.position;
  in_ident  : ident;
  in_params : param list;
  in_def    : (Loc.position * ident * term) list;
}
[@@deriving sexp_of]

(** Arguments of [meta] declarations *)
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
[@@deriving sexp_of]

(** The possible [clone] substitution elements *)
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
[@@deriving sexp_of]

(** top-level declarations *)
type decl =
  | Dtype of type_decl list
  (** Type declaration *)
  | Dlogic of logic_decl list
  (** Collection of [function]s and [predicate]s, mutually recursively declared *)
  | Dind of Decl.ind_sign * ind_decl list
  (** An inductive or co-inductive predicate *)
  | Dprop of Decl.prop_kind * ident * term
  (** Propositions: [lemma] or [goal] or [axiom] *)
  | Dlet of ident * ghost * Expr.rs_kind * expr
  (** Global program variable *)
  | Drec of fundef list
  (** Program functions, mutually recursively defined *)
  | Dexn of ident * pty * Ity.mask
  (** Declaration of global exceptions *)
  | Dmeta of ident * metarg list
  (** Declaration of a [meta] *)
  | Dcloneexport of qualid * clone_subst list
  (** [clone export] *)
  | Duseexport of qualid
  (** [use export] *)
  | Dcloneimport of Loc.position * bool * qualid * ident option * clone_subst list
  (** [clone import ... as ...] *)
  | Duseimport of Loc.position * bool * (qualid * ident option) list
  (** [use import ... as ...] *)
  | Dimport of qualid
  (** [import] *)
  | Dscope of Loc.position * bool * ident * decl list
  (** [scope] *)
[@@deriving sexp_of]

type mlw_file =
  | Modules of (ident * decl list) list
  (** a list of modules containing lists of declarations *)
  | Decls of decl list
  (** a list of declarations outside any module *)
[@@deriving sexp_of]

