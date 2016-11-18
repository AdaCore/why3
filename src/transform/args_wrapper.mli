
open Ident
open Task

exception Arg_trans of string
exception Arg_trans_term of (string * string option * string option)
exception Arg_trans_type of (string * string option * string option)
exception Arg_hyp_not_found of string
exception Arg_bad_hypothesis of (string * string option)

exception Arg_parse_error of string*string
exception Arg_expected of string
exception Arg_theory_not_found of string

(** Pre-processing of tasks, to build unique names for all declared
    identifiers of a task.*)

type id_decl = (Decl.decl list) Ident.Mid.t

type name_tables = {
    namespace : Theory.namespace;
    known_map : Decl.known_map;
    printer : ident_printer;
    id_decl : id_decl;
  }

val build_name_tables : Task.task -> name_tables

type (_, _) trans_typ =
  | Ttrans    : (task Trans.trans, task) trans_typ
  | Ttrans_l  : (task Trans.tlist, task list) trans_typ
  | Tint      : ('a, 'b) trans_typ -> ((int -> 'a), 'b) trans_typ
  | Tty       : ('a, 'b) trans_typ -> ((Ty.ty -> 'a), 'b) trans_typ
  | Ttysymbol : ('a, 'b) trans_typ -> ((Ty.tysymbol -> 'a), 'b) trans_typ
  | Tprsymbol : ('a, 'b) trans_typ -> ((Decl.prsymbol -> 'a), 'b) trans_typ
  | Tterm     : ('a, 'b) trans_typ -> ((Term.term -> 'a), 'b) trans_typ
  | Tstring   : ('a, 'b) trans_typ -> ((string -> 'a), 'b) trans_typ
  | Tformula  : ('a, 'b) trans_typ -> ((Term.term -> 'a), 'b) trans_typ
  | Ttheory   : ('a, 'b) trans_typ -> ((Theory.theory -> 'a), 'b) trans_typ
  | Tenv      : ('a, 'b) trans_typ -> ((Env.env -> 'a), 'b) trans_typ
  | Topt      : string * ('a -> 'c, 'b) trans_typ -> (('a option -> 'c), 'b) trans_typ
  | Toptbool  : string * ('a, 'b) trans_typ -> (bool -> 'a, 'b) trans_typ

(** wrap arguments of transformations, turning string arguments into
    arguments of proper types.  arguments of type term of formula are
    parsed and typed, name resolution using the given name_tables. *)

val wrap_l : ('a, task list) trans_typ -> 'a -> Trans.trans_with_args_l

val wrap   : ('a, task) trans_typ -> 'a -> Trans.trans_with_args
