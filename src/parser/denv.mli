
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


(** Destructive environments *)

type denv = { 
  th : theory_uc; (* the theory under construction *)
  utyvars : (string, type_var) Hashtbl.t; (* user type variables *)
  dvars : dty Mstr.t; (* local variables, to be bound later *)
}

val create_denv : theory_uc -> denv

val dty : denv -> Ptree.pty -> dty

val ty_of_dty : dty -> ty


(** Lookup *)

val find_tysymbol_ns : Ptree.qualid -> namespace -> tysymbol
val find_lsymbol_ns : Ptree.qualid -> namespace -> lsymbol
val find_prop_ns : Ptree.qualid -> namespace -> Decl.prop

val find_tysymbol : Ptree.qualid -> theory_uc -> tysymbol
val find_lsymbol :  Ptree.qualid -> theory_uc -> lsymbol
val find_prop : Ptree.qualid -> theory_uc -> Decl.prop


(** Specialization *)

val specialize_tysymbol : 
  loc:Ptree.loc -> Ptree.qualid -> denv -> Ty.tysymbol * type_var list

val specialize_lsymbol  : 
  loc:Ptree.loc -> lsymbol -> lsymbol * dty list * dty option


(** Error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit

