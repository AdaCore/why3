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
  | PEset of pexpr * (ident * term) list
  | PElet of pexpr * pvar list
  | PEcut of term * pexpr (* { t } e *)
  | PEbox of pexpr (* ! e *)
  | PEwox of pexpr (* ? e *)
  | PEany (* any *)

and pargument =
  | PAt of pty (* < ty > *)
  | PAv of term (* t *)
  | PAr of ident (* &r *)
  | PAc of pexpr (* (e) *)

and pvar = ident * term * pty * bool

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

type pdecl =
  | Def of pdefn
  | Blo of pdefn list
  (* | Lets of pvar  list *)
  | Pld of decl
  | Use of Loc.position * use

type pfile = pdecl list

open Ty
open Term

type hsymbol = {
  hs_name : Ident.ident;
}

let create_hsymbol id = { hs_name = Ident.id_register id }

let hs_to_merge = (Ident.Wid.create 256 : unit Ident.Wid.t)

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
  | Elet of expr * (vsymbol * term * bool) list
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

(* typed ast printer *)
module PP = struct
  open Format

  let pr = Ident.create_ident_printer []

  let pp_osp    fmt c      = if c then fprintf fmt " "
  let pp_sp_nl2 fmt ()     = pp_print_break fmt 1 2

  let pp_tv   fmt t = fprintf fmt "<%a>"        Pretty.print_tv t
  let pp_ty   fmt t = fprintf fmt "<%a>"        Pretty.print_ty t
  let pp_hs   fmt h = fprintf fmt "%s"          (Ident.id_unique pr h.hs_name)
  let pp_term fmt t = fprintf fmt "{%a}"        Pretty.print_term t
  let pp_ofty fmt t = fprintf fmt ": @[%a@]" Pretty.print_ty t
  let pp_pval fmt v = fprintf fmt "{%a%a}"      Pretty.print_vs v pp_ofty v.vs_ty
  let pp_var mut fmt v = fprintf fmt "%s%a"     (if mut then "&" else "") Pretty.print_vs v

  let rec pp_hdl fmt (i, w, pl) = fprintf fmt "(%a @[<h>[%a]@]%a%a)" pp_hs i pp_prew w pp_osp (pl <> []) pp_prms pl

  and pp_prew fmt w =
    let pp_sep fmt () = fprintf fmt " " in
    let pp_v fmt s = fprintf fmt "%a" Pretty.print_vs s in
    pp_print_list ~pp_sep pp_v fmt w

  and pp_prms fmt pl =
    let pp_sep fmt () = fprintf fmt " " in
    pp_print_list ~pp_sep pp_param fmt pl

  and pp_param fmt = function
    | Pt t -> fprintf fmt "%a"  pp_tv        t
    | Pv v -> fprintf fmt "%a"  pp_pval      v
    | Pr r -> fprintf fmt "%a" (pp_var true) r
    | Pc h -> fprintf fmt "%a"  pp_hdl       h

  let pp_set fmt sl =
    let pp_sep fmt () = fprintf fmt "@ |" in
    let pp_v fmt (s, t) = fprintf fmt "@ %a <-@ %a" (pp_var true) s pp_term t in
    pp_print_list ~pp_sep pp_v fmt sl

  let pp_let fmt sl =
    let pp_sep fmt () = fprintf fmt "@ |" in
    let pp_v fmt (s, t, mut) = fprintf fmt "@ %a =@ %a" (pp_var mut) s pp_term t in
    pp_print_list ~pp_sep pp_v fmt sl

  let rec pp_expr fmt = function
    | Eany           -> fprintf fmt "any"
    | Esym i         -> fprintf fmt "%a"             pp_hs i
    | Ebox e         -> fprintf fmt "(↑@ @[%a@])"    pp_expr e
    | Ewox e         -> fprintf fmt "(↓@ @[%a@])"    pp_expr e
    | Eset (e, l)    -> fprintf fmt "%a@\n[%a]"      pp_expr e pp_set l
    | Elet (e, l)    -> fprintf fmt "%a@\n[%a]"      pp_expr e pp_let l
    | Eapp (e, arg)  -> fprintf fmt "@[%a%a@[%a@]@]" pp_expr e pp_sp_nl2 () pp_arg arg
    | Ecut (t, e)    -> fprintf fmt "%a@ %a"         pp_term t pp_expr e
    | Edef (e, b, l) -> fprintf fmt "%a@\n[%a]"      pp_expr e (pp_local_defs_block b)  l
    | Elam (p, e)    -> fprintf fmt "(fu@[n %a%a→@ @[%a@]@])"  pp_prms p pp_osp (p <> []) pp_expr e

  and pp_arg fmt = function
    | At t        -> fprintf fmt "%a"   pp_ty  t
    | Av v        -> fprintf fmt "%a"   pp_term v
    | Ar r        -> fprintf fmt "%a"   (pp_var true) r
    | Ac (Esym i) -> fprintf fmt "%a"   pp_hs i
    | Ac e        -> fprintf fmt "(%a)" pp_expr e

  and pp_def direct fmt (h, w, pl, e) =
    fprintf fmt "%a [%a] %a%a%s%a@[%a@]"
      pp_hs h
      pp_prew w
      pp_prms pl
      pp_osp (pl <> [])
      (if direct then "→" else "=")
      pp_sp_nl2 ()
      pp_expr e

  and pp_local_defs_block direct fmt l =
    let pp_sep fmt () = fprintf fmt "@\n|" in
    let pp_v fmt d = fprintf fmt " %a" (pp_def direct) d in
    pp_print_list ~pp_sep pp_v fmt l

  and pp_def_block fmt = function
    | [d] -> fprintf fmt "let %a" (pp_def false) d
    | l   ->
        let pp_sep fmt () = fprintf fmt "@\nwith " in
        let pp_v fmt d = fprintf fmt "%a" (pp_def false) d in
        pp_print_string fmt "let rec ";
        pp_print_list ~pp_sep pp_v fmt l
end

(* parsed ast printer *)
module PPp = struct
  open Format

  let pr = Ident.create_ident_printer []

  let pp_osp    fmt c      = if c then fprintf fmt " "
  let pp_sp_nl2 fmt ()     = pp_print_break fmt 1 2
  let pp_var mut fmt i = fprintf fmt "%s%s"     (if mut then "&" else "") i.id_str

  let pp_prew fmt w =
    let pp_sep fmt () = fprintf fmt " " in
    pp_print_list ~pp_sep pp_print_string fmt (List.map (fun e -> e.id_str) w)

  let rec pp_param fmt = function
    | PPt i
    | PPr (i,_)
    | PPv (i,_) -> fprintf fmt "%s" i.id_str
    | PPc (i, idl, pl) -> fprintf fmt "(%s [%a] %a)" i.id_str pp_prew idl (pp_print_list pp_param) pl

  let pp_set fmt sl =
    let pp_sep fmt () = fprintf fmt "@ |" in
    let pp_v fmt (s, t) = fprintf fmt "@ %a <-@ {}" (pp_var true) s in
    pp_print_list ~pp_sep pp_v fmt sl

  let pp_let fmt sl =
    let pp_sep fmt () = fprintf fmt "@ |" in
    let pp_v fmt (s, _, _, mut) = fprintf fmt "@ %a =@ {}" (pp_var mut) s in
    pp_print_list ~pp_sep pp_v fmt sl

  let rec pp_expr fmt e = match e.pexpr_desc with
    | PEany           -> fprintf fmt "any"
    | PEsym i         -> fprintf fmt "%s"             i.id_str
    | PEbox e         -> fprintf fmt "(↑@ @[%a@])"    pp_expr e
    | PEwox e         -> fprintf fmt "(↓@ @[%a@])"    pp_expr e
    | PEset (e, l)    -> fprintf fmt "%a@\n[%a]"      pp_expr e pp_set l
    | PElet (e, l)    -> fprintf fmt "%a@\n[%a]"      pp_expr e pp_let l
    | PEapp (e, arg)  -> fprintf fmt "@[%a%a@[%a@]@]" pp_expr e pp_sp_nl2 () pp_arg arg
    | PEcut (t, e)    -> fprintf fmt "assert {}@ %a"  pp_expr e
    | PEdef (e, b, l) -> fprintf fmt "%a@\n[%a]"      pp_expr e (pp_local_defs_block b)  l
    | PElam (p, e)    -> fprintf fmt "(fu@[n %a%a→@ @[%a@]@])"  (pp_print_list pp_param) p pp_osp (p <> []) pp_expr e

  and pp_arg fmt = function
    | PAt _        -> fprintf fmt "<pty>"
    | PAv _        -> fprintf fmt "{}"
    | PAr r        -> fprintf fmt "%a"  (pp_var true) r
    | PAc e        -> fprintf fmt "(%a)" pp_expr e

  and pp_def direct fmt d =
    let { pdefn_name; pdefn_writes ; pdefn_params ; pdefn_body  } = d.pdefn_desc in
    fprintf fmt "%s [%a] %a%a%s%a@[%a@]"
      pdefn_name.id_str
      pp_prew pdefn_writes
      (pp_print_list pp_param) pdefn_params
      pp_osp (pdefn_params <> [])
      (if direct then "→" else "=")
      pp_sp_nl2 ()
      pp_expr pdefn_body

  and pp_local_defs_block direct fmt l =
    let pp_sep fmt () = fprintf fmt "@\n|" in
    let pp_v fmt d = fprintf fmt " %a" (pp_def direct) d in
    pp_print_list ~pp_sep pp_v fmt l

  and pp_def_block fmt = function
    | [d] -> fprintf fmt "let %a" (pp_def false) d
    | l   ->
        let pp_sep fmt () = fprintf fmt "@\nwith " in
        let pp_v fmt d = fprintf fmt "%a" (pp_def false) d in
        pp_print_string fmt "let rec ";
        pp_print_list ~pp_sep pp_v fmt l
end
