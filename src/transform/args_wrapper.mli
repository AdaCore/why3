(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)




(** Pre-processing of transformations with arguments, including
parsing and typing in the context of a task.*)

open Task

(** {2 context for parsing/typing transformation arguments} *)

exception Parse_error of string
exception Arg_expected of string * string
exception Arg_theory_not_found of string
exception Arg_expected_none of string
exception Arg_pr_not_found of Decl.prsymbol
exception Arg_qid_not_found of Ptree.qualid
exception Arg_error of string
exception Arg_parse_type_error of Loc.position * string * exn
exception Unnecessary_arguments of string list


val build_naming_tables : Task.task -> Trans.naming_table
(** builds a naming tabl from a task, suitable for both parsing/typing
transformation arguments and for printing the task, with coherent
identifiers names. *)

type symbol =
  | Tstysymbol of Ty.tysymbol
  | Tsprsymbol of Decl.prsymbol
  | Tslsymbol of Term.lsymbol

val find_symbol : string -> Trans.naming_table -> symbol

(** {2 transformation types}

transformations with argument are themselves given types to control
the interpretation of their raw string arguments. The type [trans_typ]
of such transformations is elegantly defined as a GADT *)

type (_, _) trans_typ =
  | Ttrans      : ((task Trans.trans), task) trans_typ
  (** transformation with no argument, and exactly one resulting task *)
  | Ttrans_l    : ((task Trans.tlist), task list) trans_typ
  (** transformation with no argument, and many resulting tasks *)
  | Tenvtrans   : (Env.env -> (task Trans.trans), task) trans_typ
  (** transformation with no argument but depending on the
      environment, and exactly one resulting task *)
  | Tenvtrans_l : (Env.env -> (task Trans.tlist), task list) trans_typ
  (** transformation with no argument but depending on the
      environment, and many resulting tasks *)
  | Tstring     : ('a, 'b) trans_typ -> ((string -> 'a), 'b) trans_typ
  (** transformation with a string as argument *)
  | Tint        : ('a, 'b) trans_typ -> ((int -> 'a), 'b) trans_typ
  (** transformation with an integer argument *)
  | Tty         : ('a, 'b) trans_typ -> ((Ty.ty -> 'a), 'b) trans_typ
  (** transformation with a Why3 type as argument *)
  | Ttysymbol   : ('a, 'b) trans_typ -> ((Ty.tysymbol -> 'a), 'b) trans_typ
  (** transformation with a Why3 type symbol as argument *)
  | Tprsymbol   : ('a, 'b) trans_typ -> ((Decl.prsymbol -> 'a), 'b) trans_typ
  (** transformation with a Why3 proposition symbol as argument *)
  | Tprlist     : ('a, 'b) trans_typ -> ((Decl.prsymbol list -> 'a), 'b) trans_typ
  (** transformation with a list of Why3 proposition symbols as
      argument. The symbols must be separated by commas *)
  | Tlsymbol    : ('a, 'b) trans_typ -> ((Term.lsymbol -> 'a), 'b) trans_typ
  (** transformation with a Why3 logic symbol as argument *)
  | Tsymbol     : ('a, 'b) trans_typ -> ((symbol -> 'a), 'b) trans_typ
  (** transformation with a Why3 symbol as argument, either a type
      symbol, a logic symbol or a proposotion symbol *)
  | Tlist       : ('a, 'b) trans_typ -> ((symbol list -> 'a), 'b) trans_typ
  (** transformation with a list Why3 symbol as argument, either a
      type symbol, a logic symbol or a proposotion symbol. The symbols
      must be separated by commas *)
  | Tidentlist : ('a, 'b) trans_typ -> ((string list -> 'a), 'b) trans_typ
  (** transformation with a list of identifiers as argument. The identifiers do not need
      to exist in the task, typically they could be fresh symbols *)
  | Ttermlist   : ('a, 'b) trans_typ -> ((Term.term list -> 'a), 'b) trans_typ
  (** transformation with a list of terms as argument. *)
  | Tterm       : ('a, 'b) trans_typ -> ((Term.term -> 'a), 'b) trans_typ
  (** transformation with a Why3 term as argument *)
  | Tformula    : ('a, 'b) trans_typ -> ((Term.term -> 'a), 'b) trans_typ
  (** transformation with a Why3 formula as argument *)
  | Ttheory     : ('a, 'b) trans_typ -> ((Theory.theory -> 'a), 'b) trans_typ
  (** transformation with a Why3 theory name as argument *)
  | Topt        : string * ('a -> 'c, 'b) trans_typ -> (('a option -> 'c), 'b) trans_typ
  (** transformation with an optional argument. The first string is
      the keyword introducing that optional argument*)
  | Toptbool    : string * ('a, 'b) trans_typ -> (bool -> 'a, 'b) trans_typ
  (** transformation with an optional boolean argument. The first
      string is the keyword for that optional argument, its presence
      meaning "true" *)

(** {2 parsing and typing of arguments}

the functions below wrap arguments of transformations, turning string
    arguments into arguments of proper types.  arguments of type term
    of formula are parsed and typed, name resolution using the proper
    naming table. *)

val wrap_l : ('a, task list) trans_typ -> 'a -> Trans.trans_with_args_l

val wrap   : ('a, task) trans_typ -> 'a -> Trans.trans_with_args

val wrap_and_register : desc:Pp.formatted -> string -> ('a, 'b) trans_typ -> 'a -> unit
