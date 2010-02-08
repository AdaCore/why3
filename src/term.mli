
type label

type vsymbol = Name.t
type vsymbol_set = Name.S.t

module Ty : sig

  type tysymbol = private {
    ty_name : Name.t;
    ty_args : vsymbol list;
    ty_def  : ty option;
  }

  and ty = private { 
    ty_node : ty_node; 
    ty_tag : int; 
  } 

  and ty_node = private
    | Tyvar of vsymbol
    | Tyapp of tysymbol * ty list

  val create_tysymbol : Name.t -> vsymbol list -> ty option -> tysymbol

  val ty_var : vsymbol -> ty
  val ty_app : tysymbol -> ty list -> ty

end

type tysymbol = Ty.tysymbol
type ty = Ty.ty

type fsymbol = private {
  f_name   : Name.t;
  f_scheme : ty list * ty;
}

type psymbol = private {
  p_name   : Name.t;
  p_scheme : ty list;
}

type quant = 
  | Fforall
  | Fexists

type binop = 
  | Fand
  | For
  | Fimplies
  | Fiff

type unop =
  | Fnot

type term = private { 
  t_node : term_node; 
  t_label : label;
  t_ty : ty;
  t_tag : int;
}

and fmla = private {
  f_node : fmla_node;
  f_label : label;
  f_tag : int;
}

and term_node = private
  | Tbvar of int * int
  | Tvar of vsymbol
  | Tapp of fsymbol * term list
  | Tcase of term * tbranch list
  | Tlet of term * bind_term
  | Teps of bind_fmla

and fmla_node = private
  | Fapp of psymbol * term list
  | Fquant of quant * bind_fmla
  | Fbinop of binop * fmla * fmla
  | Funop of unop * fmla
  | Ftrue
  | Ffalse
  | Fif of fmla * fmla * fmla
  | Flet of term * bind_fmla
  | Fcase of term * fbranch list

and bind_term

and tbranch

and bind_fmla

and fbranch


(* patterns *)

type pattern

val pat_wild : pattern
val pat_var : vsymbol -> pattern
val pat_app : fsymbol -> pattern list -> pattern
val pat_as : pattern -> vsymbol -> pattern

(* smart constructors for term *)

val t_var : vsymbol -> ty -> term
val t_app : fsymbol -> term list -> term
val t_case : term -> (pattern * term) list -> term
val t_let : vsymbol -> term -> term -> term
val t_eps : fmla -> term

(* smart constructors for fmla *)

val f_app : psymbol -> term list -> fmla
val f_forall : vsymbol -> ty -> fmla -> fmla
val f_exists : vsymbol -> ty -> fmla -> fmla
val f_and : fmla -> fmla -> fmla
val f_or_ : fmla -> fmla -> fmla
val f_implies : fmla -> fmla -> fmla
val f_iff : fmla -> fmla -> fmla
val f_true : fmla
val f_false : fmla
val f_if : fmla -> fmla -> fmla -> fmla
val f_let : vsymbol -> term -> fmla -> fmla
val f_case :  term -> (pattern * fmla) list -> fmla

(* transformations ? *)

(* val map : (term -> term) -> term -> term *)

(* bindings *)

val open_bind_term : bind_term -> vsymbol * term
val open_tbranch : tbranch -> vsymbol_set * pattern * term

val open_fmla : bind_fmla -> vsymbol * fmla
val open_fbranch : fbranch -> vsymbol_set * pattern * fmla

(* equality *)

val t_equal : term -> term -> bool
val t_alpha_equal : term -> term -> bool

val f_equal : fmla -> fmla -> bool
val f_alpha_equal : fmla -> fmla -> bool

(* pretty-printers *)

val print_term : Format.formatter -> term -> unit
val print_fmla : Format.formatter -> fmla -> unit


