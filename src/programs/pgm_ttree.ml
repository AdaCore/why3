(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Why
open Pgm_types
open Pgm_types.T

type loc = Loc.position

type ident = Ptree.ident

type constant = Term.constant

type assertion_kind = Ptree.assertion_kind

type lazy_op = Ptree.lazy_op

type for_direction = Ptree.for_direction

(*****************************************************************************)
(* phase 1: introduction of destructive types *)

type dreference =
  | DRlocal  of string
  | DRglobal of psymbol

type deffect = {
  de_reads  : dreference list;
  de_writes : dreference list;
  de_raises : esymbol list;
}

type dpre = Denv.dfmla

type dpost_fmla = Denv.dty * Denv.dfmla
type dexn_post_fmla = Denv.dty option * Denv.dfmla
type dpost = dpost_fmla * (Term.lsymbol * dexn_post_fmla) list

type dtype_v =
  | DTpure  of Denv.dty
  | DTarrow of dbinder list * dtype_c

and dtype_c =
  { dc_result_type : dtype_v;
    dc_effect      : deffect;
    dc_pre         : dpre;
    dc_post        : dpost; }

and dbinder = ident * Denv.dty * dtype_v

type dvariant = Denv.dterm * Term.lsymbol

type dloop_annotation = {
  dloop_invariant : Denv.dfmla option;
  dloop_variant   : dvariant option;
}

type dexpr = {
  dexpr_desc : dexpr_desc;
  dexpr_denv : Typing.denv;
  dexpr_type : Denv.dty;
  dexpr_loc  : loc;
}

and dexpr_desc =
  | DEconstant of constant
  | DElocal of string * Denv.dty
  | DEglobal of psymbol * dtype_v
  | DElogic of Term.lsymbol
  | DEapply of dexpr * dexpr
  | DEfun of dbinder list * dtriple
  | DElet of ident * dexpr * dexpr
  | DEletrec of drecfun list * dexpr

  | DEsequence of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEloop of dloop_annotation * dexpr
  | DElazy of lazy_op * dexpr * dexpr
  | DEmatch of dexpr * (Denv.dpattern * dexpr) list
  | DEabsurd
  | DEraise of esymbol * dexpr option
  | DEtry of dexpr * (esymbol * string option * dexpr) list
  | DEfor of ident * dexpr * for_direction * dexpr * Denv.dfmla option * dexpr

  | DEassert of assertion_kind * Denv.dfmla
  | DElabel of string * dexpr
  | DEany of dtype_c

and drecfun = (ident * Denv.dty) * dbinder list * dvariant option * dtriple

and dtriple = dpre * dexpr * dpost

(*****************************************************************************)
(* phase 2: removal of destructive types *)

type variant = Term.term * Term.lsymbol

type reference = R.t

type pre = T.pre

type post = T.post

(* each program variable is materialized by two logic variables (vsymbol):
   one for typing programs and another for typing annotations *)
type ivsymbol = { 
  i_pgm   : Term.vsymbol; (* in programs *)
  i_logic : Term.vsymbol; (* in annotations *)
}

type ireference =
  | IRlocal  of ivsymbol
  | IRglobal of psymbol

type ieffect = {
  ie_reads  : ireference list;
  ie_writes : ireference list;
  ie_raises : esymbol list;
}

type itype_v =
  | ITpure  of Ty.ty
  | ITarrow of ibinder list * itype_c

and itype_c =
  { ic_result_type : itype_v;
    ic_effect      : ieffect;
    ic_pre         : pre;
    ic_post        : post; }

and ibinder = ivsymbol * itype_v

type loop_annotation = {
  loop_invariant : Term.fmla option;
  loop_variant   : variant option;
}

type label = Term.vsymbol

type irec_variant = ivsymbol * Term.term * Term.lsymbol

type ipattern = {
  ipat_pat  : Term.pattern;
  ipat_node : ipat_node;
}

and ipat_node = 
  | IPwild
  | IPvar  of ivsymbol
  | IPapp  of Term.lsymbol * ipattern list
  | IPor   of ipattern * ipattern
  | IPas   of ipattern * ivsymbol

type iexpr = {
  iexpr_desc : iexpr_desc;
  iexpr_type : Ty.ty;
  iexpr_loc  : loc;
}

and iexpr_desc =
  | IElogic of Term.term
  | IElocal of ivsymbol
  | IEglobal of psymbol
  | IEapply of iexpr * ivsymbol
  | IEapply_ref of iexpr * ireference
  | IEfun of ibinder list * itriple
  | IElet of ivsymbol * iexpr * iexpr
  | IEletrec of irecfun list * iexpr

  | IEif of iexpr * iexpr * iexpr
  | IEloop of loop_annotation * iexpr
  | IElazy of lazy_op * iexpr * iexpr
  | IEmatch of ivsymbol * (ipattern * iexpr) list
  | IEabsurd
  | IEraise of esymbol * iexpr option
  | IEtry of iexpr * (esymbol * ivsymbol option * iexpr) list
  | IEfor of ivsymbol * ivsymbol * for_direction * ivsymbol *
             Term.fmla option * iexpr

  | IEassert of assertion_kind * Term.fmla
  | IElabel of label * iexpr
  | IEany of itype_c

and irecfun = ivsymbol * ibinder list * irec_variant option * itriple

and itriple = pre * iexpr * post


(*****************************************************************************)
(* phase 3: effect inference *)

type rec_variant = pvsymbol * Term.term * Term.lsymbol

type pattern = {
  ppat_pat  : Term.pattern;
  ppat_node : ppat_node;
}

and ppat_node = 
  | Pwild
  | Pvar  of pvsymbol
  | Papp  of Term.lsymbol * pattern list
  | Por   of pattern * pattern
  | Pas   of pattern * pvsymbol

type expr = {
  expr_desc  : expr_desc;
  expr_type  : Ty.ty;
  expr_type_v: type_v;
  expr_effect: E.t;
  expr_loc   : loc;
}

and expr_desc =
  | Elogic of Term.term
  | Elocal of pvsymbol
  | Eglobal of psymbol
  | Efun of pvsymbol list * triple
  | Elet of pvsymbol * expr * expr
  | Eletrec of recfun list * expr

  | Eif of expr * expr * expr
  | Eloop of loop_annotation * expr
  | Ematch of pvsymbol * (pattern * expr) list
  | Eabsurd
  | Eraise of esymbol * expr option
  | Etry of expr * (esymbol * pvsymbol option * expr) list
  | Efor of pvsymbol * pvsymbol * for_direction * pvsymbol *
            Term.fmla option * expr

  | Eassert of assertion_kind * Term.fmla
  | Elabel of label * expr
  | Eany of type_c

and recfun = pvsymbol * pvsymbol list * rec_variant option * triple

and triple = pre * expr * post

type decl =
  | Dlet    of T.psymbol * expr
  | Dletrec of (T.psymbol * recfun) list
  | Dparam  of T.psymbol * type_v

type file = decl list


(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
