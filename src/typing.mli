
open Term

(** typing environments *)

type env

val empty : env

val find_tysymbol : string -> env -> tysymbol
val find_fsymbol : string -> env -> fsymbol
val find_psymbol : string -> env -> psymbol
val find_tyvar : string -> env -> vsymbol
val find_var : string -> env -> vsymbol

(** typing *)

val term : env -> Ptree.lexpr -> term
val fmla : env -> Ptree.lexpr -> fmla

(** building environments *)

val add : env -> Ptree.logic_decl ->env

(** error reporting *)

type error

exception Error of error

val report : Format.formatter -> error -> unit
