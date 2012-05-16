(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

open Format
open Why3
open Pp
open Util
open Ident
open Ty
open Term
open Theory
open Pretty
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl
open Mlw_module

let debug_print_labels = Debug.register_flag "print_labels"
let debug_print_locs = Debug.register_flag "print_locs"
let debug_print_reg_types = Debug.register_flag "print_reg_types"

let rprinter =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer [] ~sanitizer:isanitize

let forget_regs () = Ident.forget_all rprinter
let forget_tvs_regs () = Ident.forget_all rprinter; forget_tvs ()
let forget_all () = Ident.forget_all rprinter; forget_all ()

(* ghost regions are prefixed with "?" *)
let print_reg fmt reg =
  fprintf fmt "%s" (id_unique rprinter reg.reg_name)

let print_pv fmt pv =
  fprintf fmt "%s%a" (if pv.pv_vtv.vtv_ghost then "?" else "")
    print_vs pv.pv_vs

let forget_pv pv = forget_var pv.pv_vs

(* theory names always start with an upper case letter *)
let print_mod fmt m = print_th fmt m.mod_theory

let print_its fmt ts = print_ts fmt ts.its_pure

(** Types *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_ity_node inn fmt ity = match ity.ity_node with
  | Ityvar v -> print_tv fmt v
  | Itypur (ts,tl) when is_ts_tuple ts -> fprintf fmt "(%a)"
      (print_list comma (print_ity_node false)) tl
  | Itypur (ts,[]) -> print_ts fmt ts
  | Itypur (ts,tl) -> fprintf fmt (protect_on inn "%a@ %a")
      print_ts ts (print_list space (print_ity_node true)) tl
  | Ityapp (ts,[],rl) -> fprintf fmt (protect_on inn "%a@ <%a>")
      print_its ts (print_list comma print_regty) rl
  | Ityapp (ts,tl,rl) -> fprintf fmt (protect_on inn "%a@ <%a>@ %a")
      print_its ts (print_list comma print_regty) rl
      (print_list space (print_ity_node true)) tl

and print_regty fmt reg =
  if Debug.test_flag debug_print_reg_types then print_reg fmt reg else
  fprintf fmt "%a:@,%a" print_reg reg (print_ity_node false) reg.reg_ity

let print_ity = print_ity_node false

let print_reg_opt fmt = function
  | Some r -> fprintf fmt "<%a>" print_regty r
  | None -> ()

(*
let print_pvty fmt pv = fprintf fmt "%a%a:@,%a"
  print_pv pv print_reg_opt pv.pv_mutable print_ity pv.pv_ity
*)

(* Labels and locs - copied from Pretty *)

let print_labels = print_iter1 Slab.iter space print_label

let print_ident_labels fmt id =
  if Debug.test_flag debug_print_labels &&
      not (Slab.is_empty id.id_label) then
    fprintf fmt "@ %a" print_labels id.id_label;
  if Debug.test_flag debug_print_locs then
    Util.option_iter (fprintf fmt "@ %a" print_loc) id.id_loc

(** Type declarations *)

let print_tv_arg fmt tv = fprintf fmt "@ %a" print_tv tv
let print_ty_arg fmt ty = fprintf fmt "@ %a" (print_ity_node true) ty

let print_constr fmt (cs,pjl) =
  let print_pj fmt (vtv,pj) = match pj with
    | Some { pl_ls = ls } ->
        fprintf fmt "@ (%s%s%a%a:@,%a)"
          (if vtv.vtv_ghost then "ghost " else "")
          (if vtv.vtv_mut <> None then "mutable " else "")
          print_ls ls print_reg_opt vtv.vtv_mut print_ity vtv.vtv_ity
    | None when vtv.vtv_ghost || vtv.vtv_mut <> None ->
        fprintf fmt "@ (%s%s%a@ %a)"
          (if vtv.vtv_ghost then "ghost" else "")
          (if vtv.vtv_mut <> None then "mutable " else "")
          print_reg_opt vtv.vtv_mut
          print_ity vtv.vtv_ity
    | None ->
        print_ty_arg fmt vtv.vtv_ity
  in
  fprintf fmt "@[<hov 4>| %a%a%a@]" print_cs cs.pl_ls
    print_ident_labels cs.pl_ls.ls_name
    (print_list nothing print_pj)
    (List.map2 (fun vtv pj -> (vtv,pj)) cs.pl_args pjl)

let print_head fst fmt ts =
  fprintf fmt "%s %s%s%a%a <%a>%a"
    (if fst then "type" else "with")
    (if ts.its_abst then "abstract " else "")
    (if ts.its_priv then "private " else "")
    print_its ts
    print_ident_labels ts.its_pure.ts_name
    (print_list comma print_regty) ts.its_regs
    (print_list nothing print_tv_arg) ts.its_args

let print_ty_decl fmt ts = match ts.its_def with
  | None ->
      fprintf fmt "@[<hov 2>%a@]" (print_head true) ts
  | Some ty ->
      fprintf fmt "@[<hov 2>%a =@ %a@]" (print_head true) ts print_ity ty

let print_ty_decl fmt ts =
  print_ty_decl fmt ts; forget_tvs_regs ()

let print_data_decl fst fmt (ts,csl) =
  fprintf fmt "@[<hov 2>%a =@\n@[<hov>%a@]@]"
    (print_head fst) ts (print_list newline print_constr) csl;
  forget_tvs_regs ()

(* Declarations *)

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r -> print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let print_pdecl fmt d = match d.pd_node with
  | PDtype ts -> print_ty_decl fmt ts
  | PDdata tl -> print_list_next newline print_data_decl fmt tl

let print_next_data_decl  = print_data_decl false
let print_data_decl       = print_data_decl true

let print_module fmt m =
  fprintf fmt "@[<hov 2>module %a%a@\n%a@]@\nend@."
    print_mod m print_ident_labels m.mod_theory.th_name
    (print_list newline2 print_pdecl) m.mod_decls

(* Print exceptions *)

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | BadItyArity (ts, ts_arg, app_arg) ->
      fprintf fmt "Bad type arity: type symbol %a must be applied \
                   to %i arguments, but is applied to %i"
        print_its ts ts_arg app_arg
  | BadRegArity (ts, ts_arg, app_arg) ->
      fprintf fmt "Bad region arity: type symbol %a must be applied \
                   to %i regions, but is applied to %i"
        print_its ts ts_arg app_arg
  | DuplicateRegion r ->
      fprintf fmt "Region %a is used twice" print_reg r
  | UnboundRegion r ->
      fprintf fmt "Unbound region %a" print_reg r
  | RegionMismatch (r1,r2) ->
      fprintf fmt "Region mismatch between %a and %a"
        print_regty r1 print_regty r2
  | Mlw_ty.TypeMismatch (t1,t2) ->
      fprintf fmt "Type mismatch between %a and %a"
        print_ity t1 print_ity t2
  | _ -> raise exn
  end
