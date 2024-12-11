(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3

type pvar =
  Ptree.ident * Ptree.term * Ptree.pty * bool

type pparam =
  | PPt of Ptree.ident
  | PPv of Ptree.ident * Ptree.pty
  | PPr of Ptree.ident * Ptree.pty
  | PPc of
      Ptree.ident * Ptree.ident list * pparam list
  | PPa of Ptree.term * bool
  | PPo
  | PPb
  | PPl of pvar list

type pexpr = {
  pexpr_desc : pexpr_desc;
  pexpr_loc : Loc.position;
}

and pexpr_desc =
  | PEsym of Ptree.qualid
  | PEapp of pexpr * pargument
  | PElam of pparam list * pexpr
  | PEdef of pexpr * bool * pdefn list
  | PEset of pexpr * (Ptree.ident * Ptree.term) list
  | PElet of pexpr * pvar list
  | PEcut of (Ptree.term * bool) list * pexpr
  | PEbox of pexpr
  | PEwox of pexpr
  | PEany

and pargument =
  | PAt of Ptree.pty
  | PAv of Ptree.term
  | PAr of Ptree.ident
  | PAc of pexpr

and pdefn = {
  pdefn_desc : pdefn_desc;
  pdefn_loc : Loc.position;
}

and pdefn_desc = {
  pdefn_name : Ptree.ident;
  pdefn_writes : Ptree.ident list;
  pdefn_params : pparam list;
  pdefn_body : pexpr;
}

type use =
  | Puseexport of Ptree.qualid
  | Puseimport of
      bool * Ptree.qualid * Ptree.ident option

type pdecl =
  | Blo of pdefn list
  | Mlw of Ptree.decl
  | Use of use

type pfile = (Ptree.ident * pdecl list) list

module PP : sig
  open Format

  val pr : Ident.ident_printer

  val pp_osp    : formatter -> bool -> unit
  val pp_sp_nl2 : formatter -> unit -> unit
  val pp_tv     : formatter -> Ty.tvsymbol -> unit
  val pp_ty     : formatter -> Ty.ty -> unit
  val pp_hs     : formatter -> Coma_logic.hsymbol -> unit
  val pp_term   : formatter -> Term.term -> unit
  val pp_ofty   : formatter -> Ty.ty -> unit
  val pp_pval   : formatter -> Term.vsymbol -> unit

  val pp_var :
    bool -> formatter -> Term.vsymbol -> unit

  val pp_hdl :
    formatter ->
    Coma_logic.hsymbol
    * Term.vsymbol list
    * Coma_logic.param list ->
    unit

  val pp_prew  : formatter -> Term.vsymbol list -> unit
  val pp_prms  : formatter -> Coma_logic.param list -> unit
  val pp_param : formatter -> Coma_logic.param -> unit

  val pp_set :
    formatter ->
    (Term.vsymbol * Term.term) list ->
    unit

  val pp_let :
    formatter ->
    (Term.vsymbol * Term.term * bool) list ->
    unit

  val pp_annot : bool -> formatter -> Term.term -> unit

  val pp_expr : formatter -> Coma_logic.expr -> unit
  val pp_arg  : formatter -> Coma_logic.argument -> unit

  val pp_def : bool -> formatter -> Coma_logic.defn -> unit

  val pp_local_defs_block : bool -> formatter -> Coma_logic.defn list -> unit

  val pp_def_block : formatter -> Coma_logic.defn list -> unit
end

module PPp : sig
  open Format

  val pr : Ident.ident_printer

  val pp_osp    : formatter -> bool -> unit
  val pp_sp_nl2 : formatter -> unit -> unit

  val pp_var : bool -> formatter -> Ptree.ident -> unit

  val pp_prew  : formatter -> Ptree.ident list -> unit
  val pp_param : formatter -> pparam -> unit
  val pp_set   : formatter -> (Ptree.ident * 'a) list -> unit
  val pp_let   : formatter -> (Ptree.ident * 'a * 'b * bool) list -> unit

  val pp_annot : bool -> formatter -> 'a -> unit
  val pp_expr  : formatter -> pexpr -> unit
  val pp_arg   : formatter -> pargument -> unit
  val pp_def   : bool -> formatter -> pdefn -> unit

  val pp_local_defs_block : bool -> formatter -> pdefn list -> unit

  val pp_def_block : formatter -> pdefn list -> unit
end

