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

open Why3
open Ptree

type pparam =
  | PPt of ident (* < 'a > *)
  | PPv of ident * pty (* x *)
  | PPr of ident * pty (* &r *)
  | PPc of ident * ident list * pparam list (* x [x...] p... *)

type pexpr = {
  pexpr_desc : pexpr_desc;
  pexpr_loc  : Loc.position;
}

and pexpr_desc =
  | PEsym of ident (* x *)
  | PEapp of pexpr * pargument (* e <ty>... t... | e... *)
  | PElam of pparam list * pexpr (* fun pl -> e *)
  | PEdef of pexpr * bool * pdefn list (* e / rec? h p = e and ... *)
  | PEset of pexpr * (ident * term * pty) list (* assign ... *)
  | PEcut of term * pexpr (* { t } e *)
  | PEbox of pexpr (* ! e *)
  | PEwox of pexpr (* ? e *)
  | PEany (* any *)

and pargument =
  | PAt of pty (* < ty > *)
  | PAv of term (* t *)
  | PAr of ident (* &r *)
  | PAc of pexpr (* (e) *)

and pdefn = {
  pdefn_desc   : pdefn_desc;
  pdefn_loc    : Loc.position;
}

and pdefn_desc = {
  pdefn_name   : ident;
  pdefn_writes : ident list;
  pdefn_params : pparam list;
  pdefn_body   : pexpr;
}

type use =
  | Puseexport of qualid
  | Puseimport of bool * qualid * ident option

type pfile = use list * pdefn list

open Ty
open Term

type hsymbol = {
  hs_name : Ident.ident;
}

let create_hsymbol id = { hs_name = Ident.id_register id }

type param =
  | Pt of tvsymbol
  | Pv of vsymbol
  | Pr of vsymbol
  | Pc of (hsymbol * vsymbol list * param list)

type expr =
  | Esym of hsymbol
  | Eapp of expr * argument
  | Elam of param list * expr
  | Edef of expr * bool * defn list
  | Eset of expr * (vsymbol * term) list
  | Ecut of term * expr
  | Ebox of expr
  | Ewox of expr
  | Eany

and argument =
  | At of ty
  | Av of term
  | Ar of vsymbol
  | Ac of expr

and defn = hsymbol * vsymbol list * param list * expr

open Format

let pr = Ident.create_ident_printer []

let pp_osp    fmt c      = if c then fprintf fmt " "
let pp_sp_nl2 fmt ()     = pp_print_break fmt 1 2

let pp_tv   fmt t = fprintf fmt "<%a>"        Pretty.print_tv t
let pp_ty   fmt t = fprintf fmt "<%a>"        Pretty.print_ty t
let pp_ref  fmt v = fprintf fmt "&%a"         Pretty.print_vs v
let pp_hsym fmt h = fprintf fmt "%s"          (Ident.id_unique pr h.hs_name)
let pp_term fmt t = fprintf fmt "{%a}"        Pretty.print_term t
let pp_ofty fmt t = fprintf fmt ": @[<h>%a@]" Pretty.print_ty t
let pp_pval fmt v = fprintf fmt "{%a%a}"      Pretty.print_vs v pp_ofty v.vs_ty
let pp_eqto fmt d = fprintf fmt "%s"          (if d then "→" else "=")

let rec pp_hdl fmt (i, w, pl) = fprintf fmt "(%a @[<h>[%a]@]%a%a)" pp_hsym i pp_prew w pp_osp (pl <> []) pp_prms pl

and pp_prew fmt w =
  let pp_v fmt s = fprintf fmt "%a" Pretty.print_vs s in
  pp_print_list ~pp_sep:pp_print_space pp_v fmt w

and pp_prms fmt pl =
  let pp_sep fmt () = fprintf fmt " " in
  pp_print_list ~pp_sep pp_param fmt pl

and pp_param fmt = function
  | Pt t -> fprintf fmt "%a" pp_tv   t
  | Pv v -> fprintf fmt "%a" pp_pval v
  | Pr r -> fprintf fmt "%a" pp_ref  r
  | Pc h -> fprintf fmt "%a" pp_hdl  h

let pp_set fmt sl =
  let pp_sep fmt () = fprintf fmt "@\n" in
  let pp_v fmt (s, t) = fprintf fmt "/ %a =@ %a" pp_ref s pp_term t in
  pp_print_list ~pp_sep pp_v fmt sl

let rec pp_expr fmt = function
  | Eany           -> fprintf fmt "any"
  | Esym i         -> fprintf fmt "%a"                  pp_hsym i
  | Ebox e         -> fprintf fmt "↑@ @[%a@]"           pp_expr e
  | Ewox e         -> fprintf fmt "↓@ @[%a@]"           pp_expr e
  | Eset (e, l)    -> fprintf fmt "%a@\n%a"             pp_expr e pp_set l
  | Eapp (e, arg)  -> fprintf fmt "@[%a%a@[%a@]@]"      pp_expr e pp_sp_nl2 () pp_arg arg
  | Elam (p, e)    -> fprintf fmt "(fu@[n %a%a→@ @[%a@]@])" pp_prms p pp_osp (p <> []) pp_expr e
  | Ecut (t, e)    -> fprintf fmt "%a@ %a"              pp_term t pp_expr e
  | Edef (e, b, l) -> fprintf fmt "%a@\n%a"             pp_expr e (pp_defs b)  l

and pp_arg fmt = function
  | At t -> fprintf fmt "%a" pp_ty  t
  | Av v -> fprintf fmt "%a" pp_term v
  | Ar r -> fprintf fmt "%a" pp_ref r
  | Ac e ->
      match e with
      | Esym i -> fprintf fmt "%a" pp_hsym i
      | _ -> fprintf fmt "(%a)" pp_expr e

and pp_def direct fmt (h, w, pl, e) =
  fprintf fmt "%a @[<h>[%a]@] %a%a%a%a@[%a@]"
    pp_hsym h
    pp_prew w
    pp_prms pl
    pp_osp (pl <> [])
    pp_eqto direct
    pp_sp_nl2 ()
    pp_expr e

and pp_defs direct fmt l =
  let pp_sep fmt () = fprintf fmt "@\n" in
  let pp_v fmt d = fprintf fmt "/ %a" (pp_def direct) d in
  pp_print_list ~pp_sep pp_v fmt l
