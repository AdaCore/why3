
(** Types *)

type tvsymbol = Name.t

(* type symbols and types *)

type tysymbol = private {
  ts_name : Name.t;
  ts_args : tvsymbol list;
  ts_def  : ty option;
  ts_tag  : int;
}

and ty = private {
  ty_node : ty_node;
  ty_tag  : int;
}

and ty_node = private
  | Tyvar of tvsymbol
  | Tyapp of tysymbol * ty list

exception NonLinear
exception UnboundTypeVariable

val create_tysymbol : Name.t -> tvsymbol list -> ty option -> tysymbol

module Sts : Set.S with type elt = tysymbol
module Mts : Map.S with type key = tysymbol

exception BadTypeArity

val ty_var : tvsymbol -> ty
val ty_app : tysymbol -> ty list -> ty

val ty_map : (ty -> ty) -> ty -> ty
val ty_fold : ('a -> ty -> 'a) -> 'a -> ty -> 'a
val ty_forall : (ty -> bool) -> ty -> bool
val ty_exists : (ty -> bool) -> ty -> bool

exception TypeMismatch

val matching : ty Name.M.t -> ty -> ty -> ty Name.M.t
val ty_match : ty -> ty -> ty Name.M.t -> ty Name.M.t option

