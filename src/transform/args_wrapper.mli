
open Ident
open Task

(** Pre-processing of tasks, to build unique names for all declared
    identifiers of a task.*)

type name_tables = {
    namespace : Theory.namespace;
    known_map : Decl.known_map;
    printer : ident_printer;
  }

val build_name_tables : Task.task -> name_tables

type _ trans_typ =
  | Ttrans : (task -> task list) trans_typ
  | Tint : 'a trans_typ -> (int -> 'a) trans_typ
(*
  | Tstring : 'a trans_typ -> (string -> 'a) trans_typ
*)
  | Tty : 'a trans_typ -> (Ty.ty -> 'a) trans_typ
  | Ttysymbol : 'a trans_typ -> (Ty.tysymbol -> 'a) trans_typ
  | Tprsymbol : 'a trans_typ -> (Decl.prsymbol -> 'a) trans_typ
  | Tterm : 'a trans_typ -> (Term.term -> 'a) trans_typ
  | Tformula : 'a trans_typ -> (Term.term -> 'a) trans_typ

(** wrap arguments of transformations, turning string arguments into
    arguments of proper types.  arguments of type term of formula are
    parsed and typed, name resolution using the given name_tables. *)

val wrap : (* name_tables -> *) 'a trans_typ -> 'a -> Trans.trans_with_args
