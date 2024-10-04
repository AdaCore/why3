(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

type ty =
  | Tvar of Ty.tvsymbol
  | Tapp of Ident.ident * ty list
  | Tarrow of ty * ty
  | Ttuple of ty list

val pp_ty : ty Pp.pp

type is_ghost = bool

type var = Ident.ident * ty * is_ghost

type for_direction = To | DownTo

type pat =
  | Pwild
  | Pvar of Term.vsymbol
  | Papp of Term.lsymbol * pat list
  | Ptuple of pat list
  | Por of pat * pat
  | Pas of pat * Term.vsymbol

type is_rec = bool

type is_partial = bool

type binop = Band | Bor | Beq

type ity = I of Ity.ity | C of Ity.cty

type expr = {
  e_node : expr_node;
  e_ity : ity;
  e_mlty : ty;
  e_effect : Ity.effekt;
  e_attrs : Ident.Sattr.t;
}
and expr_node =
  | Econst of Constant.constant
  | Evar of Ity.pvsymbol
  | Eapp of Expr.rsymbol * expr list * is_partial
  | Efun of var list * expr
  | Elet of let_def * expr
  | Eif of expr * expr * expr
  | Eassign of (expr * ty * Expr.rsymbol * expr) list
  | Ematch of expr * reg_branch list * exn_branch list
  | Eblock of expr list
  | Ewhile of expr * expr
  | Efor of Ity.pvsymbol * ty * Ity.pvsymbol * for_direction * Ity.pvsymbol * expr
  | Eraise of Ity.xsymbol * expr option
  | Eexn of Ity.xsymbol * ty option * expr
  | Eignore of expr
  | Eabsurd
and reg_branch = pat * expr
and exn_branch = Ity.xsymbol * Ity.pvsymbol list * expr
and let_def =
  | Lvar of Ity.pvsymbol * expr
  | Lsym of Expr.rsymbol * Ty.Stv.t * ty * var list * expr
  | Lany of Expr.rsymbol * Ty.Stv.t * ty * var list
  | Lrec of rdef list
and rdef = {
  rec_sym : Expr.rsymbol;
  rec_args : var list;
  rec_exp : expr;
  rec_res : ty;
  rec_svar : Ty.Stv.t;
}

type is_mutable = bool

type typedef =
  | Ddata of (Ident.ident * ty list) list
  | Drecord of (is_mutable * Ident.ident * ty) list
  | Dalias of ty
  | Drange of Number.int_range
  | Dfloat of Number.float_format

type its_defn = private {
  its_name : Ident.ident;
  its_args : Ty.tvsymbol list;
  its_private : bool;
  its_def : typedef option;
}

type decl =
  | Dtype of its_defn list
  | Dlet of let_def
  | Dval of Ity.pvsymbol * ty
  | Dexn of Ity.xsymbol * ty option
  | Dmodule of string * decl list

type from_module = {
  from_mod : Pmodule.pmodule option;
  from_km : Pdecl.known_map;
}

type known_map = decl Ident.Mid.t

type pmodule = {
  mod_from : from_module;
  mod_decl : decl list;
  mod_known : known_map;
}

val get_decl_name : decl -> Ident.ident list

val add_known_decl : decl -> decl Ident.Mid.t -> Ident.Mid.key -> decl Ident.Mid.t

val iter_deps : (Ident.ident -> unit) -> decl -> unit

val ity_unit : ity

val mk_expr : expr_node -> ity -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val tunit : ty

val is_unit : ity -> bool

val is_true : expr -> bool

val is_false : expr -> bool

val t_arrow : ty -> ty -> ty

val t_fun : var list -> ty -> ty

val mk_var : Ident.ident -> ty -> is_ghost -> var

val mk_var_unit : var

val mk_its_defn : Ident.ident -> Ty.tvsymbol list -> bool -> typedef option -> its_defn

val dummy_expr_attr : Ident.attribute

val e_dummy_unit : expr

val e_unit : expr

val e_const : Constant.constant -> ity -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val e_var : Ity.pvsymbol -> ity -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val var_defn : Ity.pvsymbol -> expr -> let_def

val sym_defn : Expr.rsymbol -> Ty.Stv.t -> ty -> var list -> expr -> let_def

val e_let : let_def -> expr -> ity -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val e_app : Expr.rsymbol -> expr list -> is_partial -> ity -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val e_fun : var list -> expr -> ity -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val e_ignore : expr -> expr

val e_if : expr -> expr -> expr -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val e_while : expr -> expr -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val e_for : Ity.pvsymbol -> ty -> Ity.pvsymbol -> for_direction -> Ity.pvsymbol -> expr -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val e_match : expr -> reg_branch list -> exn_branch list -> ity -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val e_assign : (expr * ty * Expr.rsymbol * expr) list -> ity -> Ity.mask -> Ity.effekt -> Ident.Sattr.t -> expr

val e_absurd : ity -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val e_seq : expr -> expr -> ity -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val e_coerce : expr -> ity -> Ity.mask -> ty -> Ity.effekt -> Ident.Sattr.t -> expr

val var_list_of_pv_list : Ity.pvsymbol list -> ty list -> expr list

val ld_map : (expr -> expr) -> let_def -> let_def

val e_map : (expr -> expr) -> expr -> expr

val ld_fold : ('a -> expr -> 'a) -> 'a -> let_def -> 'a

val e_fold : ('a -> expr -> 'a) -> 'a -> expr -> 'a

val ld_map_fold : ('a -> expr -> 'a * expr) -> 'a -> let_def -> 'a * let_def

val e_map_fold : ('a -> expr -> 'a * expr) -> 'a -> expr -> 'a * expr
