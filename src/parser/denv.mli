
open Util
open Ty
open Term
open Theory

(** Destructive unification *)

type type_var

type dty = 
  | Tyvar of type_var
  | Tyapp of tysymbol * dty list

val create_ty_decl_var : ?loc:Ptree.loc -> user:bool -> tvsymbol -> type_var

val unify : dty -> dty -> bool

val print_dty : Format.formatter -> dty -> unit

val ty_of_dty : dty -> ty

(** Specialization *)

val specialize_tysymbol : 
  loc:Ptree.loc -> tysymbol -> type_var list

val specialize_lsymbol  : 
  loc:Ptree.loc -> lsymbol -> dty list * dty option


(** Error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit

