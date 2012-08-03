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
  fprintf fmt "@[%a:@,%a@]" print_reg reg (print_ity_node false) reg.reg_ity

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
        fprintf fmt "{refresh %a@ under %a}@ " print_regty r print_regty u
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
  let print_arg fmt pv = fprintf fmt "%a ->@ " print_vtv pv.pv_vtv in
  fprintf fmt "%a%a%a" (print_list nothing print_arg) vta.vta_args
    print_effect vta.vta_spec.c_effect print_vty vta.vta_result

and print_vty fmt = function
  | VTarrow vta -> print_vta fmt vta
  | VTvalue vtv -> print_vtv fmt vtv

let print_pvty fmt pv = fprintf fmt "@[%a%a:@,%a@]"
  print_pv pv print_reg_opt pv.pv_vtv.vtv_mut print_vtv pv.pv_vtv

let print_psty fmt ps =
  let print_tvs fmt tvs = if not (Stv.is_empty tvs) then
    fprintf fmt "[%a]@ " (print_list comma print_tv) (Stv.elements tvs) in
  let print_regs fmt regs = if not (Sreg.is_empty regs) then
    fprintf fmt "<%a>@ " (print_list comma print_regty) (Sreg.elements regs) in
  let vars = vta_vars ps.ps_vta in
  fprintf fmt "@[%a :@ %a%a%a@]"
    print_ps ps
    print_tvs (Mtv.set_diff vars.vars_tv ps.ps_subst.ity_subst_tv)
    print_regs (Mreg.set_diff vars.vars_reg ps.ps_subst.ity_subst_reg)
    print_vta ps.ps_vta

(* specification *)

let print_post fmt post =
  let vs,f = open_post post in
  fprintf fmt "@[%a ->@ %a@]" print_vs vs print_term f;
  Pretty.forget_var vs

let print_lv fmt = function
  | LetV pv -> print_pvty fmt pv
  | LetA ps -> print_psty fmt ps

let forget_lv = function
  | LetV pv -> forget_pv pv
  | LetA ps -> forget_ps ps

let rec print_type_v fmt = function
  | VTvalue vtv -> print_vtv fmt vtv
  | VTarrow vta ->
      let print_arg fmt pv = fprintf fmt "@[(%a)@] ->@ " print_pvty pv in
      fprintf fmt "%a%a"
        (print_list nothing print_arg) vta.vta_args
        (print_type_c vta.vta_spec) vta.vta_result;
      List.iter forget_pv vta.vta_args

and print_type_c spec fmt vty =
  fprintf fmt "{ %a }@ %a%a@ { %a }"
    print_term spec.c_pre
    print_effect spec.c_effect
    print_type_v vty
    print_post spec.c_post
    (* TODO: print_xpost *)

let print_invariant fmt f =
  fprintf fmt "invariant@ { %a }@ " Pretty.print_term f

let print_variant fmt varl =
  let print_rel fmt = function
    | Some ps -> fprintf fmt "@ [%a]" Pretty.print_ls ps
    | None -> () in
  let print_var fmt (t, ps) =
    fprintf fmt " %a%a" Pretty.print_term t print_rel ps in
  fprintf fmt "variant@ {%a }@ " (print_list comma print_var) varl

let print_invariant fmt f = match f.t_node with
  | Ttrue -> ()
  | _ -> print_invariant fmt f

let print_variant fmt = function
  | [] -> ()
  | varl -> print_variant fmt varl

(* expressions *)

let print_ppat fmt ppat = print_pat fmt ppat.ppat_pattern

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
  | Eapp (e,v,_) ->
      fprintf fmt "(%a@ %a)" (print_lexpr pri) e print_pv v
  | Elet ({ let_sym = LetV pv ; let_expr = e1 }, e2)
    when pv.pv_vs.vs_name.id_string = "_" &&
         ity_equal pv.pv_vtv.vtv_ity ity_unit ->
      fprintf fmt (protect_on (pri > 0) "%a;@\n%a")
        print_expr e1 print_expr e2;
  | Elet ({ let_sym = lv ; let_expr = e1 }, e2) ->
      fprintf fmt (protect_on (pri > 0) "@[<hov 2>let %a =@ %a@ in@]@\n%a")
        print_lv lv (print_lexpr 4) e1 print_expr e2;
      forget_lv lv
  | Erec ({ rec_defn = rdl; rec_letrec = lr }, e) ->
      fprintf fmt (protect_on (pri > 0) "%a@ in@\n%a")
        (print_list_next newline (print_rec lr)) rdl print_expr e;
      let forget_rd rd = forget_ps rd.fun_ps in
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
  | Eloop (inv,var,e) ->
      fprintf fmt "loop@ %a%a@\n@[<hov>%a@]@\nend"
        print_invariant inv print_variant var print_expr e
  | Efor (pv,(pvfrom,dir,pvto),inv,e) ->
      fprintf fmt "@[<hov 2>for@ %a =@ %a@ %s@ %a@ %ado@\n%a@]@\ndone"
        print_pv pv print_pv pvfrom
        (if dir = To then "to" else "downto") print_pv pvto
        print_invariant inv print_expr e
  | Eraise (xs,e) ->
      fprintf fmt "raise (%a %a)" print_xs xs print_expr e
  | Etry (e,bl) ->
      fprintf fmt "try %a with@\n@[<hov>%a@]@\nend"
        print_expr e (print_list newline print_xbranch) bl
  | Eabsurd ->
      fprintf fmt "absurd"
  | Eassert (ak,f) ->
      fprintf fmt "%a { %a }" print_ak ak print_term f
  | Eabstr (e,q,_xq) ->
    (* TODO: print_xpost *)
      fprintf fmt "abstract %a@ { %a }" print_expr e print_post q
  | Eghost e ->
      fprintf fmt "ghost@ %a" print_expr e
  | Eany spec ->
      fprintf fmt "any@ %a" (print_type_c spec) e.e_vty

and print_branch fmt ({ ppat_pattern = p }, e) =
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_expr e;
  Svs.iter forget_var p.pat_vars

and print_xbranch fmt (xs, pv, e) =
  fprintf fmt "@[<hov 4>| %a %a ->@ %a@]" print_xs xs print_pv pv print_expr e;
  forget_pv pv

and print_rec lr fst fmt { fun_ps = ps ; fun_lambda = lam } =
  let print_arg fmt pv = fprintf fmt "@[(%a)@]" print_pvty pv in
  fprintf fmt "@[<hov 2>%s (%a)@ %a =@\n{ %a }@\n%a%a@\n{ %a }@]"
    (if fst then if lr > 0 then "let rec" else "let" else "with")
    print_psty ps
    (print_list space print_arg) lam.l_args
    print_term lam.l_pre
    print_variant lam.l_variant
    print_expr lam.l_expr
    print_post lam.l_post
    (* TODO: print_xpost *)

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

let print_data_decl fst fmt (ts,csl,inv) =
  let print_inv fmt inv = if ts.its_inv then
    fprintf fmt "@ invariant { %a }" print_post inv else () in
  fprintf fmt "@[<hov 2>%a =@ %a%a@]"
    (print_head fst) ts (print_list newline print_constr) csl
    print_inv inv;
  forget_tvs_regs ()

let print_val_decl fmt lv =
  let vty = match lv with
    | LetV pv -> VTvalue pv.pv_vtv | LetA ps -> VTarrow ps.ps_vta in
  fprintf fmt "@[<hov 2>val (%a) :@ %a@]" print_lv lv print_type_v vty;
  (* FIXME: don't forget global regions *)
  forget_tvs_regs ()

let print_let_decl fmt { let_sym = lv ; let_expr = e } =
  fprintf fmt "@[<hov 2>let %a =@ %a@]" print_lv lv print_expr e;
  (* FIXME: don't forget global regions *)
  forget_tvs_regs ()

let print_rec_decl lr fst fmt rd =
  print_rec lr fst fmt rd;
  forget_tvs_regs ()

let print_exn_decl fmt xs =
  fprintf fmt "@[<hov 2>exception %a of@ %a@]"
    print_xs xs print_ity xs.xs_ity

(* Declarations *)

let print_pdecl fmt d = match d.pd_node with
  | PDtype ts -> print_ty_decl fmt ts
  | PDdata tl -> print_list_next newline print_data_decl fmt tl
  | PDval  vd -> print_val_decl fmt vd
  | PDlet  ld -> print_let_decl fmt ld
  | PDrec { rec_defn = rdl; rec_letrec = lr } ->
      print_list_next newline (print_rec_decl lr) fmt rdl
  | PDexn  xs -> print_exn_decl fmt xs

(* Print exceptions *)

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | Mlw_ty.BadItyArity (ts, ts_arg, app_arg) ->
      fprintf fmt "Bad type arity: type symbol %a must be applied \
                   to %i arguments, but is applied to %i"
        print_its ts ts_arg app_arg
  | Mlw_ty.BadRegArity (ts, ts_arg, app_arg) ->
      fprintf fmt "Bad region arity: type symbol %a must be applied \
                   to %i regions, but is applied to %i"
        print_its ts ts_arg app_arg
  | Mlw_ty.DuplicateRegion r ->
      fprintf fmt "Region %a is used twice" print_reg r
  | Mlw_ty.UnboundRegion r ->
      fprintf fmt "Unbound region %a" print_reg r
  | Mlw_ty.UnboundException xs ->
      fprintf fmt "This function raises %a but does not \
        specify a post-condition for it" print_xs xs
  | Mlw_ty.RegionMismatch (r1,r2) ->
      fprintf fmt "Region mismatch between %a and %a"
        print_regty r1 print_regty r2
  | Mlw_ty.TypeMismatch (t1,t2) ->
      fprintf fmt "Type mismatch between %a and %a"
        print_ity t1 print_ity t2
  | Mlw_ty.PolymorphicException (id,_ity) ->
      fprintf fmt "Exception %s has a polymorphic type" id.id_string
  | Mlw_ty.MutableException (id,_ity) ->
      fprintf fmt "The type of exception %s has mutable components" id.id_string
  | Mlw_ty.IllegalAlias _reg ->
      fprintf fmt "This application creates an illegal alias"
  | Mlw_expr.RdOnlyPLS _ls ->
      fprintf fmt "Cannot construct values of a private type"
  | Mlw_expr.HiddenPLS ls ->
      fprintf fmt "'%a' is a constructor/field of an abstract type \
      and cannot be used in a program" print_ls ls;
  | Mlw_expr.GhostWrite (_e, _reg) ->
      fprintf fmt "This expression stores a ghost value in a non-ghost location"
  | Mlw_expr.GhostRaise (_e, xs) ->
      fprintf fmt "This expression raises a ghost exception %a \
        catched by a non-ghost code" print_xs xs
  | Mlw_expr.StaleRegion (_e, id) ->
      fprintf fmt "This expression prohibits further \
        usage of variable %s" id.id_string
  | Mlw_expr.ValueExpected _e ->
      fprintf fmt "This expression is not a first-order value"
  | Mlw_expr.ArrowExpected _e ->
      fprintf fmt "This expression is not a function and cannot be applied"
  | Mlw_expr.Immutable _e ->
      fprintf fmt "Mutable expression expected"
  | _ -> raise exn
  end
