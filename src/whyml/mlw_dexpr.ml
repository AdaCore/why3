(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ty
open Term
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

(** Program types *)

type dity

let dity_fresh _ = assert false (* unit -> dity *)

let dity_of_ity _ = assert false (* ity -> dity *)

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)

(** Patterns *)

type dpattern = {
  dp_pat  : pre_ppattern;
  dp_dity : dity;
  dp_loc  : Loc.position option;
}

type dpattern_node =
  | DPwild
  | DPvar  of preid
  | DPlapp of lsymbol * dpattern list
  | DPpapp of plsymbol * dpattern list
  | DPor   of dpattern * dpattern
  | DPas   of dpattern * preid

(** Specifications *)

type ghost = bool

type dbinder = preid * ghost * dity

type 'a later = vsymbol Mstr.t -> 'a
  (* specification terms are parsed and typechecked after the program
     expressions, when the types of locally bound program variables are
     already established. *)

type dspec = {
  ds_pre     : pre;
  ds_post    : post;
  ds_xpost   : xpost;
  ds_reads   : vsymbol list;
  ds_writes  : term list;
  ds_variant : variant list;
}

type dtype_v =
  | DSpecV of dity
  | DSpecA of dbinder list * dtype_c

and dtype_c = dtype_v * dspec later

(** Expressions *)

type dlazy_op = DEand | DEor

type dexpr = {
  de_node : dexpr_node;
  de_dvty : dvty;
  de_loc  : Loc.position option;
}

and dexpr_node =
  | DEvar of string * dvty
  | DEgpvar of pvsymbol
  | DEgpsym of psymbol
  | DEplapp of plsymbol * dexpr list
  | DElsapp of lsymbol * dexpr list
  | DEapply of dexpr * dexpr list
  | DEconstant of Number.constant
  | DEval of dval_decl * dexpr
  | DElet of dlet_defn * dexpr
  | DEfun of dfun_defn * dexpr
  | DErec of dfun_defn list * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEmatch of dexpr * (dpattern * dexpr) list
  | DEassign of plsymbol * dexpr * dexpr
  | DElazy of dlazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEtrue
  | DEfalse
  | DEraise of xsymbol * dexpr
  | DEtry of dexpr * (xsymbol * dpattern * dexpr) list
  | DEfor of preid * dexpr * for_direction * dexpr * invariant later * dexpr
  | DEloop of variant list later * invariant later * dexpr
  | DEabsurd
  | DEassert of assertion_kind * term later
  | DEabstract of dexpr * dspec later
  | DEmark of preid * dexpr
  | DEghost of dexpr
  | DEany of dtype_c
  | DEcast of dexpr * ity
  | DEuloc of dexpr * Loc.position
  | DElabel of dexpr * Slab.t

and dval_decl = preid * ghost * dtype_v

and dlet_defn = preid * ghost * dexpr

and dfun_defn = preid * ghost * dbinder list * dity * dexpr * dspec later

(** Environment *)

type denv = {
  frozen : dity list;
  locals : (Stv.t option * dvty) Mstr.t;
}

let denv_empty = { frozen = []; locals = Mstr.empty }

let denv_add_val _ = assert false (* denv -> dval_decl -> denv *)

let denv_add_let _ = assert false (* denv -> dlet_defn -> denv *)

let denv_add_fun _ = assert false (* denv -> dfun_defn -> denv *)

let denv_prepare_rec _ = assert false (* denv -> preid -> dbinder list -> dity -> denv *)

let denv_verify_rec  _ = assert false (* denv -> preid -> unit *)

let denv_add_args _ = assert false (* denv -> dbinder list -> denv *)

let denv_add_pat _ = assert false (* denv -> dpattern -> denv *)

let denv_get _ = assert false (* denv -> string -> dexpr_node (** raises UnboundVar *) *)

let denv_get_opt _ = assert false (* denv -> string -> dexpr_node option *)

(** Constructors *)

let dpattern ?loc _ = ignore(loc); assert false (* ?loc:Loc.position -> dpattern_node -> dpattern *)

let dexpr ?loc _ = ignore (loc); assert false (* ?loc:Loc.position -> dexpr_node -> dexpr *)

(** Final stage *)

let expr     ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dexpr -> expr *)
let val_decl ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dval_decl -> let_sym *)
let let_defn ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dlet_defn -> let_defn *)
let fun_defn ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dfun_defn -> fun_defn *)
let rec_defn ~strict ~keep_loc _ = ignore(strict); ignore(keep_loc); assert false (* strict:bool -> keep_loc:bool -> dfun_defn list -> fun_defn list *)
