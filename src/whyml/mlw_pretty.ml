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

let iprinter =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer [] ~sanitizer:isanitize

let rprinter =
  let isanitize = sanitizer char_to_alpha char_to_alnumus in
  create_ident_printer [] ~sanitizer:isanitize

let forget_regs () = Ident.forget_all rprinter
let forget_tvs_regs () = Ident.forget_all rprinter; forget_tvs ()
let forget_all () = Ident.forget_all rprinter; forget_all ()

(* Labels and locs - copied from Pretty *)

let print_labels = print_iter1 Slab.iter space print_label

let print_ident_labels fmt id =
  if Debug.test_flag debug_print_labels &&
      not (Slab.is_empty id.id_label) then
    fprintf fmt "@ %a" print_labels id.id_label;
  if Debug.test_flag debug_print_locs then
    Util.option_iter (fprintf fmt "@ %a" print_loc) id.id_loc

(* identifiers *)

let print_reg fmt reg =
  fprintf fmt "%s" (id_unique rprinter reg.reg_name)

let print_pv fmt pv =
  fprintf fmt "%s%a" (if pv.pv_vtv.vtv_ghost then "?" else "")
    print_vs pv.pv_vs

let forget_pv pv = forget_var pv.pv_vs

let print_name fmt id =
  fprintf fmt "%s%a" (id_unique iprinter id) print_ident_labels id

let print_xs fmt xs = print_name fmt xs.xs_name

let print_ps fmt ps =
  fprintf fmt "%s%a" (if ps.ps_vta.vta_ghost then "?" else "")
    print_name ps.ps_name

let forget_ps ps = forget_id iprinter ps.ps_name

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

let print_effect fmt eff =
  let print_xs s xs = fprintf fmt "{%s %a}@ " s print_xs xs in
  let print_reg s r = fprintf fmt "{%s %a}@ " s print_regty r in
  let print_reset r = function
    | None -> print_reg "fresh" r
    | Some u ->
        fprintf fmt "{reset %a@ under %a}@ " print_regty r print_regty u
  in
  Sreg.iter (print_reg "read") eff.eff_reads;
  Sreg.iter (print_reg "write") eff.eff_writes;
  Sexn.iter (print_xs  "raise") eff.eff_raises;
  Sreg.iter (print_reg "ghost read") eff.eff_ghostr;
  Sreg.iter (print_reg "ghost write") eff.eff_ghostw;
  Sexn.iter (print_xs  "ghost raise") eff.eff_ghostx;
  Mreg.iter print_reset eff.eff_resets

let print_vtv fmt vtv =
  fprintf fmt "%s%a" (if vtv.vtv_ghost then "?" else "") print_ity vtv.vtv_ity

let rec print_vta fmt vta =
  fprintf fmt "%a@ ->@ %a%a" print_vtv vta.vta_arg
    print_effect vta.vta_effect print_vty vta.vta_result

and print_vty fmt = function
  | VTarrow vta -> print_vta fmt vta
  | VTvalue vtv -> print_vtv fmt vtv

let print_pvty fmt pv = fprintf fmt "%a%a:@,%a"
  print_pv pv print_reg_opt pv.pv_vtv.vtv_mut print_vtv pv.pv_vtv

let print_psty fmt ps =
  let print_tvs fmt tvs = if not (Stv.is_empty tvs) then
    fprintf fmt "[%a]@ " (print_list comma print_tv) (Stv.elements tvs) in
  let print_regs fmt regs = if not (Sreg.is_empty regs) then
    fprintf fmt "<%a>@ " (print_list comma print_regty) (Sreg.elements regs) in
  let vars = ps.ps_vta.vta_vars in
  fprintf fmt "%a :@ %a%a%a"
    print_ps ps
    print_tvs (Stv.diff vars.vars_tv ps.ps_vars.vars_tv)
    print_regs (Mreg.set_diff vars.vars_reg ps.ps_subst.ity_subst_reg)
    print_vta ps.ps_vta

let print_ppat fmt ppat = print_pat fmt ppat.ppat_pattern

(* expressions *)

let print_ak fmt = function
  | Aassert -> fprintf fmt "assert"
  | Aassume -> fprintf fmt "assume"
  | Acheck  -> fprintf fmt "check"

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r -> print true fmt x; sep fmt ();
      print_list sep (print false) fmt r

let rec print_expr fmt e = print_lexpr 0 fmt e

and print_lexpr pri fmt e =
  let print_elab pri fmt e =
    if Debug.test_flag debug_print_labels && not (Slab.is_empty e.e_label)
    then fprintf fmt (protect_on (pri > 0) "@[<hov 0>%a@ %a@]")
      print_labels e.e_label (print_enode 0) e
    else print_enode pri fmt e in
  let print_eloc pri fmt e =
    if Debug.test_flag debug_print_locs && e.e_loc <> None
    then fprintf fmt (protect_on (pri > 0) "@[<hov 0>%a@ %a@]")
      (print_option print_loc) e.e_loc (print_elab 0) e
    else print_elab pri fmt e in
  print_eloc pri fmt e

(*
and print_app pri ls fmt tl = match extract_op ls, tl with
  | _, [] ->
      print_ls fmt ls
  | Some s, [t1] when tight_op s ->
      fprintf fmt (protect_on (pri > 7) "%s%a")
        s (print_lterm 7) t1
  | Some s, [t1] ->
      fprintf fmt (protect_on (pri > 4) "%s %a")
        s (print_lterm 5) t1
  | Some s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 4) "@[<hov 1>%a %s@ %a@]")
        (print_lterm 5) t1 s (print_lterm 5) t2
  | _, [t1;t2] when ls.ls_name.id_string = "mixfix []" ->
      fprintf fmt (protect_on (pri > 6) "%a[%a]")
        (print_lterm 6) t1 print_term t2
  | _, [t1;t2;t3] when ls.ls_name.id_string = "mixfix [<-]" ->
      fprintf fmt (protect_on (pri > 6) "%a[%a <- %a]")
        (print_lterm 6) t1 (print_lterm 5) t2 (print_lterm 5) t3
  | _, tl ->
      fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a@ %a@]")
        print_ls ls (print_list space (print_lterm 6)) tl
*)

and print_enode pri fmt e = match e.e_node with
  | Elogic t ->
      fprintf fmt "(%a)" print_term t
  | Evalue v ->
      print_pv fmt v
  | Earrow a ->
      print_ps fmt a
  | Eapp (e,v) ->
      fprintf fmt "(%a@ %a)" (print_lexpr pri) e print_pv v
  | Elet ({ let_var = lv ; let_expr = e1 }, e2) ->
      let print_lv fmt = function
        | LetV pv -> print_pvty fmt pv
        | LetA ps -> print_psty fmt ps in
      let forget_lv = function
        | LetV pv -> forget_pv pv
        | LetA ps -> forget_ps ps in
      fprintf fmt (protect_on (pri > 0) "let %a = @[%a@] in@ %a")
        print_lv lv (print_lexpr 4) e1 print_expr e2;
      forget_lv lv
  | Erec (rdl,e) ->
      fprintf fmt (protect_on (pri > 0) "%a@ in@ %a")
        (print_list_next newline print_rec) rdl print_expr e;
      let forget_rd rd = forget_ps rd.rec_ps in
      List.iter forget_rd rdl
  | Eif (e0,e1,e2) ->
      fprintf fmt (protect_on (pri > 0) "if %a then %a@ else %a")
        print_expr e0 print_expr e1 print_expr e2
  | Eassign (e,r,pv) ->
      fprintf fmt (protect_on (pri > 0) "%a <%a> <- %a")
        print_expr e print_regty r print_pv pv
  | Ecase (e0,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        print_expr e0 (print_list newline print_branch) bl
  | Eraise (xs,e) ->
      fprintf fmt "raise (%a %a)" print_xs xs print_expr e
  | Etry (e,bl) ->
      fprintf fmt "try %a with@\n@[<hov>%a@]@\nend"
        print_expr e (print_list newline print_xbranch) bl
  | Eabsurd ->
      fprintf fmt "absurd"
  | Eassert (ak,f) ->
      fprintf fmt "%a@ (%a)" print_ak ak print_term f
  | _ ->
      fprintf fmt "<expr TODO>"

and print_branch fmt ({ ppat_pattern = p }, e) =
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_expr e;
  Svs.iter forget_var p.pat_vars

and print_xbranch fmt (xs, pv, e) =
  fprintf fmt "@[<hov 4>| %a %a ->@ %a@]" print_xs xs print_pv pv print_expr e;
  forget_pv pv

and print_rec fst fmt { rec_ps = ps ; rec_lambda = lam } =
  let print_post fmt post =
    let vs,f = open_post post in
    fprintf fmt "%a ->@ %a" print_vs vs print_term f in
  let print_arg fmt pv = fprintf fmt "(%a)" print_pvty pv in
  fprintf fmt "@[<hov 2>%s (%a) %a =@ { %a }@ %a@ { %a }@]"
    (if fst then "let rec" else "with")
    print_psty ps
    (print_list space print_arg) lam.l_args
    print_term lam.l_pre
    print_expr lam.l_expr
    print_post lam.l_post

(*
and print_tl fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma print_term)) tl
*)

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

let print_let_decl fmt { let_var = lv ; let_expr = e } =
  let print_lv fmt = function
    | LetV pv -> print_pvty fmt pv
    | LetA ps -> print_psty fmt ps in
  fprintf fmt "@[<hov 2>let %a = @[%a@]@]" print_lv lv print_expr e;
  (* FIXME: don't forget global regions *)
  forget_tvs_regs ()

let print_rec_decl fst fmt rd =
  print_rec fst fmt rd;
  forget_tvs_regs ()

let print_exn_decl fmt xs =
  fprintf fmt "@[<hov 2>exception %a of@ %a@]"
    print_xs xs print_ity xs.xs_ity

(* Declarations *)

let print_pdecl fmt d = match d.pd_node with
  | PDtype ts -> print_ty_decl fmt ts
  | PDdata tl -> print_list_next newline print_data_decl fmt tl
  | PDlet  ld -> print_let_decl fmt ld
  | PDrec rdl -> print_list_next newline print_rec_decl fmt rdl
  | PDexn  xs -> print_exn_decl fmt xs

let print_next_data_decl = print_data_decl false
let print_data_decl      = print_data_decl true

let print_next_rec_decl  = print_rec_decl false
let print_rec_decl       = print_rec_decl true

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
