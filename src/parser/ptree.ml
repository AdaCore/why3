(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

(*s Parse trees. *)

type loc = Loc.position

(*s Logical expressions (for both terms and predicates) *)

type integer_constant = Number.integer_constant
type real_constant = Number.real_constant
type constant = Number.constant

type label =
  | Lstr of Ident.label
  | Lpos of Loc.position

type pp_quant =
  | PPforall | PPexists | PPlambda | PPfunc | PPpred

type pp_binop =
  | PPand | PPor | PPimplies | PPiff

type pp_unop =
  | PPnot

type ident = { id : string; id_lab : label list; id_loc : loc }

type qualid =
  | Qident of ident
  | Qdot of qualid * ident

type pty =
  | PPTtyvar of ident
  | PPTtyapp of pty list * qualid
  | PPTtuple of pty list

type param = ident option * pty

type pattern =
  { pat_loc : loc; pat_desc : pat_desc }

and pat_desc =
  | PPpwild
  | PPpvar of ident
  | PPpapp of qualid * pattern list
  | PPprec of (qualid * pattern) list
  | PPptuple of pattern list
  | PPpor of pattern * pattern
  | PPpas of pattern * ident

type lexpr =
  { pp_loc : loc; pp_desc : pp_desc }

and pp_desc =
  | PPvar of qualid
  | PPapp of qualid * lexpr list
  | PPtrue
  | PPfalse
  | PPconst of constant
  | PPinfix of lexpr * ident * lexpr
  | PPbinop of lexpr * pp_binop * lexpr
  | PPunop of pp_unop * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPquant of pp_quant * param list * lexpr list list * lexpr
  | PPnamed of label * lexpr
  | PPlet of ident * lexpr * lexpr
  | PPeps of ident * pty * lexpr
  | PPmatch of lexpr * (pattern * lexpr) list
  | PPcast of lexpr * pty
  | PPtuple of lexpr list
  | PPrecord of (qualid * lexpr) list
  | PPupdate of lexpr * (qualid * lexpr) list

(*s Declarations. *)

type plogic_type =
  | PPredicate of pty list
  | PFunction  of pty list * pty

type use = {
  use_theory  : qualid;
  use_as      : string;
  use_imp_exp : bool option;
    (* None = export, Some false = default, Some true = import *)
}

type clone_subst =
  | CSns    of loc * qualid option * qualid option
  | CStsym  of loc * qualid * ident list * pty
  | CSfsym  of loc * qualid * qualid
  | CSpsym  of loc * qualid * qualid
  | CSlemma of loc * qualid
  | CSgoal  of loc * qualid

type field = {
  f_loc     : loc;
  f_ident   : ident;
  f_pty     : pty;
  f_mutable : bool;
  f_ghost   : bool
}

type type_def =
  | TDabstract
  | TDalias     of pty
  | TDalgebraic of (loc * ident * param list) list
  | TDrecord    of field list

type visibility = Public | Private | Abstract

type invariant = lexpr list

type type_decl = {
  td_loc    : loc;
  td_ident  : ident;
  td_params : ident list;
  td_model  : bool;
  td_vis    : visibility;
  td_def    : type_def;
  td_inv    : invariant;
}

type logic_decl = {
  ld_loc    : loc;
  ld_ident  : ident;
  ld_params : param list;
  ld_type   : pty option;
  ld_def    : lexpr option;
}

type ind_decl = {
  in_loc    : loc;
  in_ident  : ident;
  in_params : param list;
  in_def    : (loc * ident * lexpr) list;
}

type prop_kind =
  | Kaxiom | Klemma | Kgoal

type metarg =
  | PMAts  of qualid
  | PMAfs  of qualid
  | PMAps  of qualid
  | PMApr  of qualid
  | PMAstr of string
  | PMAint of int

type use_clone = use * clone_subst list option

type decl =
  | TypeDecl of type_decl list
  | LogicDecl of logic_decl list
  | IndDecl of Decl.ind_sign * ind_decl list
  | PropDecl of prop_kind * ident * lexpr
  | Meta of ident * metarg list

(* program files *)

type assertion_kind = Aassert | Aassume | Acheck

type lazy_op = LazyAnd | LazyOr

type variant = lexpr * qualid option

type loop_annotation = {
  loop_invariant : invariant;
  loop_variant   : variant list;
}

type for_direction = To | Downto

type ghost = bool

type pre = lexpr
type post = loc * (pattern * lexpr) list
type xpost = loc * (qualid * pattern * lexpr) list

type spec = {
  sp_pre     : pre list;
  sp_post    : post list;
  sp_xpost   : xpost list;
  sp_reads   : lexpr list;
  sp_writes  : lexpr list;
  sp_variant : variant list;
}

type binder = ident * ghost * pty option

type type_v =
  | Tpure of pty
  | Tarrow of binder list * type_c

and type_c = type_v * spec

type expr = {
  expr_desc : expr_desc;
  expr_loc  : loc;
}

and expr_desc =
  (* lambda-calculus *)
  | Econstant of constant
  | Eident of qualid
  | Eapply of expr * expr
  | Efun of binder list * triple
  | Elet of ident * ghost * expr * expr
  | Eletrec of letrec list * expr
  | Etuple of expr list
  | Erecord of (qualid * expr) list
  | Eupdate of expr * (qualid * expr) list
  | Eassign of expr * qualid * expr
  (* control *)
  | Esequence of expr * expr
  | Eif of expr * expr * expr
  | Eloop of loop_annotation * expr
  | Elazy of lazy_op * expr * expr
  | Enot of expr
  | Ematch of expr * (pattern * expr) list
  | Eabsurd
  | Eraise of qualid * expr option
  | Etry of expr * (qualid * pattern * expr) list
  | Efor of ident * expr * for_direction * expr * invariant * expr
  (* annotations *)
  | Eassert of assertion_kind * lexpr
  | Emark of ident * expr
  | Ecast of expr * pty
  | Eany of type_c
  | Eghost of expr
  | Eabstract of triple
  | Enamed of label * expr

and letrec = loc * ident * ghost * binder list * triple

and triple = expr * spec

type pdecl =
  | Dlet of ident * ghost * expr
  | Dletrec of letrec list
  | Dparam of ident * ghost * type_v
  | Dexn of ident * pty

(* incremental parsing *)

type incremental = {
  open_theory     : ident -> unit;
  close_theory    : unit -> unit;
  open_module     : ident -> unit;
  close_module    : unit -> unit;
  open_namespace  : string -> unit;
  close_namespace : loc -> bool (*import:*) -> unit;
  new_decl        : loc -> decl -> unit;
  new_pdecl       : loc -> pdecl -> unit;
  use_clone       : loc -> use_clone -> unit;
}
