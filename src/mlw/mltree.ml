open Expr
open Ident
open Ty
open Ity
open Term

type ty =
  | Tvar    of tvsymbol
  | Tapp    of ident * ty list
  | Ttuple  of ty list

type is_ghost = bool

type var = ident * ty * is_ghost

type for_direction = To | DownTo

type pat =
  | Pwild
  | Pvar    of vsymbol
  | Papp    of lsymbol * pat list
  | Ptuple  of pat list
  | Por     of pat * pat
  | Pas     of pat * vsymbol

type is_rec = bool

type binop = Band | Bor | Beq

type ity = I of Ity.ity | C of Ity.cty (* TODO: keep it like this? *)

type expr = {
  e_node   : expr_node;
  e_ity    : ity;
  e_effect : effect;
  e_label  : Slab.t;
}

and expr_node =
  | Econst  of Number.integer_constant
  | Evar    of pvsymbol
  | Eapp    of rsymbol * expr list
  | Efun    of var list * expr
  | Elet    of let_def * expr
  | Eif     of expr * expr * expr
  | Eassign of (pvsymbol * rsymbol * pvsymbol) list
  | Ematch  of expr * (pat * expr) list
  | Eblock  of expr list
  | Ewhile  of expr * expr
  (* For loop for Why3's type int *)
  | Efor    of pvsymbol * pvsymbol * for_direction * pvsymbol * expr
  | Eraise  of xsymbol * expr option
  | Eexn    of xsymbol * ty option * expr
  | Etry    of expr * (xsymbol * pvsymbol list * expr) list
  | Eignore of expr
  | Eabsurd
  | Ehole

and let_def =
  | Lvar of pvsymbol * expr
  | Lsym of rsymbol * ty * var list * expr
  | Lrec of rdef list

and rdef = {
  rec_sym  : rsymbol; (* exported *)
  rec_rsym : rsymbol; (* internal *)
  rec_args : var list;
  rec_exp  : expr;
  rec_res  : ty;
  rec_svar : Stv.t; (* set of type variables *)
}

type is_mutable = bool

type typedef =
  | Ddata     of (ident * ty list) list
  | Drecord   of (is_mutable * ident * ty) list
  | Dalias    of ty

type its_defn = {
  its_name    : ident;
  its_args    : tvsymbol list;
  its_private : bool;
  its_def     : typedef option;
}

type decl =
  | Dtype   of its_defn list
  | Dlet    of let_def
  | Dexn    of xsymbol * ty option
  | Dclone  of ident * decl list
(*
    | Dfunctor of ident * (ident * decl list) list * decl list
*)

type known_map = decl Mid.t

type from_module = {
  from_mod: Pmodule.pmodule option;
  from_km : Pdecl.known_map;
}

type pmodule = {
  mod_from  : from_module;
  mod_decl  : decl list;
  mod_known : known_map;
}
