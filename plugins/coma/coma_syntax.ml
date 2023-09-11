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
  | Pc of hsymbol * vsymbol list * param list

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

let pp_hs fmt hs =
  Format.fprintf fmt "%s" (Ident.id_unique pr hs.hs_name)

let rec pp_param fmt = function
  | Pt i -> fprintf fmt "<%a>" Pretty.print_tv i
  | Pv i -> fprintf fmt "%a" Pretty.print_vs i
  | Pr i -> fprintf fmt "&%a" Pretty.print_vs i
  | Pc (i, w, pl) -> fprintf fmt "(%a [%a] %a)" pp_hs i pp_writes w pp_params pl

and pp_writes fmt w =
  let pp_sep fmt () = fprintf fmt " " in
  let pp_v fmt s = fprintf fmt "%a" Pretty.print_vs s in
  pp_print_list ~pp_sep pp_v fmt w

and pp_params fmt pl =
  let pp_sep fmt () = fprintf fmt " " in
  pp_print_list ~pp_sep pp_param fmt pl

let pp_set fmt sl =
  let pp_sep fmt () = fprintf fmt "@\n" in
  let pp_v fmt (s, t) = fprintf fmt "/ &%a = %a" Pretty.print_vs s Pretty.print_term t in
  pp_print_list ~pp_sep pp_v fmt sl

let rec pp_expr fmt = function
  | Esym i -> fprintf fmt "%a" pp_hs i
  | Eapp (e, arg) -> fprintf fmt "%a %a" pp_expr e pp_arg arg
  | Elam (p, e) -> fprintf fmt "(fun @[%a@] → @[%a@])" pp_params p pp_expr e
  | Edef (e, false, l) -> fprintf fmt "%a@\n%a" pp_expr e pp_def1s l
  | Edef (e, true, l) -> fprintf fmt "%a@\n%a" pp_expr e pp_def2s l
  | Eset (e, l) -> fprintf fmt "%a@\n%a" pp_expr e pp_set l
  | Ecut (t, e) -> fprintf fmt "{%a} @[%a@]" Pretty.print_term t pp_expr e
  | Ebox e -> fprintf fmt "↑ @[%a@]" pp_expr e
  | Ewox e -> fprintf fmt "↓ @[%a@]" pp_expr e
  | Eany -> fprintf fmt "any"

and pp_arg fmt = function
  | At ty -> fprintf fmt "<%a>" Pretty.print_ty ty
  | Av t -> fprintf fmt "{%a}" Pretty.print_term t
  | Ar i -> fprintf fmt "&%a" Pretty.print_vs i
  | Ac e ->
      match e with
      | Esym i -> fprintf fmt "%a" pp_hs i
      | _ -> fprintf fmt "(%a)" pp_expr e

and pp_def1 fmt (h, w, pl, e) =
  fprintf fmt "%a [%a] %a =@\n  @[%a@]"
    pp_hs h
    pp_writes w
    pp_params pl
    pp_expr e

and pp_def2 fmt (h, w, pl, e) =
  fprintf fmt "%a [%a] %a ->@\n  @[%a@]"
    pp_hs h
    pp_writes w
    pp_params pl
    pp_expr e

and pp_def1s fmt l =
  let pp_sep fmt () = fprintf fmt "@\n" in
  let pp_v fmt d = fprintf fmt "/ %a" pp_def1 d in
  pp_print_list ~pp_sep pp_v fmt l

and pp_def2s fmt l =
  let pp_sep fmt () = fprintf fmt "@\n" in
  let pp_v fmt d = fprintf fmt "/ %a" pp_def2 d in
  pp_print_list ~pp_sep pp_v fmt l
