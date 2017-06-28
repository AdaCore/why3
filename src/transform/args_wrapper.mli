
open Task

exception Arg_parse_error of string * string
exception Arg_expected of string * string
exception Arg_theory_not_found of string
exception Arg_expected_none of string
exception Arg_hyp_not_found of string


(** Pre-processing of tasks, to build unique names for all declared
    identifiers of a task.*)

val build_name_tables : Task.task -> Task.names_table

type symbol =
  | Tstysymbol of Ty.tysymbol
  | Tsprsymbol of Decl.prsymbol
  | Tslsymbol of Term.lsymbol

type (_, _) trans_typ =
  | Ttrans      : ((task Trans.trans), task) trans_typ
  | Ttrans_l    : ((task Trans.tlist), task list) trans_typ
  | Tenvtrans   : (Env.env -> (task Trans.trans), task) trans_typ
  | Tenvtrans_l : (Env.env -> (task Trans.tlist), task list) trans_typ
  | Tint        : ('a, 'b) trans_typ -> ((int -> 'a), 'b) trans_typ
  | Tty         : ('a, 'b) trans_typ -> ((Ty.ty -> 'a), 'b) trans_typ
  | Ttysymbol   : ('a, 'b) trans_typ -> ((Ty.tysymbol -> 'a), 'b) trans_typ
  | Tprsymbol   : ('a, 'b) trans_typ -> ((Decl.prsymbol -> 'a), 'b) trans_typ
  | Tprlist     : ('a, 'b) trans_typ -> ((Decl.prsymbol list -> 'a), 'b) trans_typ
  | Tlsymbol    : ('a, 'b) trans_typ -> ((Term.lsymbol -> 'a), 'b) trans_typ
  | Tsymbol     : ('a, 'b) trans_typ -> ((symbol -> 'a), 'b) trans_typ
  | Tlist       : ('a, 'b) trans_typ -> ((symbol list -> 'a), 'b) trans_typ
  | Tterm       : ('a, 'b) trans_typ -> ((Term.term -> 'a), 'b) trans_typ
  | Tstring     : ('a, 'b) trans_typ -> ((string -> 'a), 'b) trans_typ
  | Tformula    : ('a, 'b) trans_typ -> ((Term.term -> 'a), 'b) trans_typ
  | Ttheory     : ('a, 'b) trans_typ -> ((Theory.theory -> 'a), 'b) trans_typ
  | Topt        : string * ('a -> 'c, 'b) trans_typ -> (('a option -> 'c), 'b) trans_typ
  | Toptbool    : string * ('a, 'b) trans_typ -> (bool -> 'a, 'b) trans_typ

(** wrap arguments of transformations, turning string arguments into
    arguments of proper types.  arguments of type term of formula are
    parsed and typed, name resolution using the given name_tables. *)

val wrap_l : ('a, task list) trans_typ -> 'a -> Trans.trans_with_args_l

val wrap   : ('a, task) trans_typ -> 'a -> Trans.trans_with_args

val wrap_and_register : desc:Pp.formatted -> string -> ('a, 'b) trans_typ -> 'a -> unit
