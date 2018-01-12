(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Format
open Pp

open Ident
open Ty
open Term
open Pretty
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl

let debug_print_labels = Debug.register_info_flag "print_labels"
  ~desc:"Print@ labels@ of@ identifiers@ and@ expressions."
let debug_print_locs = Debug.register_info_flag "print_locs"
  ~desc:"Print@ locations@ of@ identifiers@ and@ expressions."
let debug_print_reg_types = Debug.register_info_flag "print_reg_types"
  ~desc:"Print@ types@ of@ regions@ (mutable@ fields)."

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
    Opt.iter (fprintf fmt "@ %a" print_loc) id.id_loc

(* identifiers *)

let print_reg fmt reg =
  fprintf fmt "%s" (id_unique rprinter reg.reg_name)

let print_pv fmt pv =
  fprintf fmt "%s%a" (if pv.pv_ghost then "?" else "")
    print_vs pv.pv_vs

let forget_pv pv = forget_var pv.pv_vs

let print_name fmt id =
  fprintf fmt "%s%a" (id_unique iprinter id) print_ident_labels id

let print_xs fmt xs = print_name fmt xs.xs_name

let print_ps fmt ps =
  fprintf fmt "%s%a" (if ps.ps_ghost then "?" else "")
    print_name ps.ps_name

let forget_ps ps = forget_id iprinter ps.ps_name

let print_its fmt ts = print_ts fmt ts.its_ts

(** Types *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_ity_node s pri fmt ity = match ity.ity_node with
  | Ityvar v ->
      begin match Mtv.find_opt v s.ity_subst_tv with
        | Some ity -> print_ity_node ity_subst_empty pri fmt ity
        | None     -> print_tv fmt v
      end
  | Itypur (ts,[t1;t2]) when ts_equal ts Ty.ts_func ->
      fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_ity_node s 1) t1 (print_ity_node s 0) t2
  | Itypur (ts,tl) when is_ts_tuple ts -> fprintf fmt "(%a)"
      (print_list comma (print_ity_node s 0)) tl
  | Itypur (ts,[]) -> print_ts fmt ts
  | Itypur (ts,tl) -> fprintf fmt (protect_on (pri > 1) "%a@ %a")
      print_ts ts (print_list space (print_ity_node s 2)) tl
  | Ityapp (ts,[],rl) -> fprintf fmt (protect_on (pri > 1) "%a@ <%a>")
      print_its ts (print_list comma print_regty)
      (List.map (fun r -> Mreg.find_def r r s.ity_subst_reg) rl)
  | Ityapp (ts,tl,rl) -> fprintf fmt (protect_on (pri > 1) "%a@ <%a>@ %a")
      print_its ts (print_list comma print_regty)
      (List.map (fun r -> Mreg.find_def r r s.ity_subst_reg) rl)
      (print_list space (print_ity_node s 2)) tl

and print_regty fmt reg =
  if Debug.test_noflag debug_print_reg_types then print_reg fmt reg
  else fprintf fmt "@[%a:@,%a@]" print_reg reg print_ity reg.reg_ity

and print_ity fmt ity = print_ity_node ity_subst_empty 2 fmt ity

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
  Sreg.iter (print_reg "write") eff.eff_writes;
  Sexn.iter (print_xs  "raise") eff.eff_raises;
  Sreg.iter (print_reg "ghost write") eff.eff_ghostw;
  Sexn.iter (print_xs  "ghost raise") eff.eff_ghostx;
  Mreg.iter print_reset eff.eff_resets

let rec print_aty fmt aty =
  let print_arg fmt pv = fprintf fmt "%a ->@ " print_ity pv.pv_ity in
  fprintf fmt "%a%a%a" (print_list nothing print_arg) aty.aty_args
    print_effect aty.aty_spec.c_effect print_vty aty.aty_result

and print_vty fmt = function
  | VTarrow aty -> print_aty fmt aty
  | VTvalue ity -> print_ity fmt ity

let print_pvty fmt pv = fprintf fmt "@[%a:@,%a@]"
  print_pv pv print_ity pv.pv_ity

let print_psty fmt ps =
  let print_tvs fmt tvs = if not (Stv.is_empty tvs) then
    fprintf fmt "[%a]@ " (print_list comma print_tv) (Stv.elements tvs) in
  let print_regs fmt regs = if not (Sreg.is_empty regs) then
    fprintf fmt "<%a>@ " (print_list comma print_regty) (Sreg.elements regs) in
  let vars = aty_vars ps.ps_aty in
  fprintf fmt "@[%a :@ %a%a%a@]"
    print_ps ps
    print_tvs (Mtv.set_diff vars.vars_tv ps.ps_subst.ity_subst_tv)
    print_regs (Mreg.set_diff vars.vars_reg ps.ps_subst.ity_subst_reg)
    print_aty ps.ps_aty

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
  | VTvalue ity -> print_ity fmt ity
  | VTarrow aty ->
      let print_arg fmt pv = fprintf fmt "@[(%a)@] ->@ " print_pvty pv in
      fprintf fmt "%a%a"
        (print_list nothing print_arg) aty.aty_args
        (print_type_c aty.aty_spec) aty.aty_result;
      List.iter forget_pv aty.aty_args

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

let is_letrec = function
  | [fd] -> fd.fun_lambda.l_spec.c_letrec <> 0
  | _ -> true

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
         ity_equal pv.pv_ity ity_unit ->
      fprintf fmt (protect_on (pri > 0) "%a;@\n%a")
        print_expr e1 print_expr e2;
  | Elet ({ let_sym = lv ; let_expr = e1 }, e2) ->
      fprintf fmt (protect_on (pri > 0) "@[<hov 2>let %a =@ %a@ in@]@\n%a")
        print_lv lv (print_lexpr 4) e1 print_expr e2;
      forget_lv lv
  | Erec (fdl, e) ->
      fprintf fmt (protect_on (pri > 0) "%a@ in@\n%a")
        (print_list_next newline (print_rec (is_letrec fdl))) fdl print_expr e;
      List.iter (fun fd -> forget_ps fd.fun_ps) fdl
  | Eif (e0,e1,e2) ->
      fprintf fmt (protect_on (pri > 0) "if %a then %a@ else %a")
        print_expr e0 print_expr e1 print_expr e2
  | Eassign (pl,e,r,pv) ->
      fprintf fmt (protect_on (pri > 0) "%a.%a <%a> <- %a")
        print_expr e print_ls pl.pl_ls print_regty r print_pv pv
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
  | Eabstr (e,spec) ->
    (* TODO: print_spec *)
      fprintf fmt "abstract %a@ { %a }" print_expr e print_post spec.c_post
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
    (if fst then if lr then "let rec" else "let" else "with")
    print_psty ps
    (print_list space print_arg) lam.l_args
    print_term lam.l_spec.c_pre
    print_variant lam.l_spec.c_variant
    print_expr lam.l_expr
    print_post lam.l_spec.c_post
    (* TODO: print_spec *)

(*
and print_tl fmt tl =
  if tl = [] then () else fprintf fmt "@ [%a]"
    (print_list alt (print_list comma print_term)) tl
*)

(** Type declarations *)

let print_tv_arg fmt tv = fprintf fmt "@ %a" print_tv tv

let print_ty_arg fmt ty =
  fprintf fmt "@ %a" (print_ity_node ity_subst_empty 2) ty

let print_constr fmt (cs,pjl) =
  let print_pj fmt (fd,pj) = match pj with
    | Some { pl_ls = ls } ->
        fprintf fmt "@ (%s%s%a%a:@,%a)"
          (if fd.fd_ghost then "ghost " else "")
          (if fd.fd_mut <> None then "mutable " else "")
          print_ls ls print_reg_opt fd.fd_mut print_ity fd.fd_ity
    | None when fd.fd_ghost || fd.fd_mut <> None ->
        fprintf fmt "@ (%s%s%a@ %a)"
          (if fd.fd_ghost then "ghost" else "")
          (if fd.fd_mut <> None then "mutable " else "")
          print_reg_opt fd.fd_mut print_ity fd.fd_ity
    | None ->
        print_ty_arg fmt fd.fd_ity
  in
  fprintf fmt "@[<hov 4>| %a%a%a@]" print_cs cs.pl_ls
    print_ident_labels cs.pl_ls.ls_name
    (print_list nothing print_pj)
    (List.map2 (fun fd pj -> (fd,pj)) cs.pl_args pjl)

let print_head fst fmt ts =
  fprintf fmt "%s %s%s%a%a <%a>%a"
    (if fst then "type" else "with")
    (if ts.its_abst then "abstract " else "")
    (if ts.its_priv then "private " else "")
    print_its ts
    print_ident_labels ts.its_ts.ts_name
    (print_list comma print_regty) ts.its_regs
    (print_list nothing print_tv_arg) ts.its_ts.ts_args

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
    | LetV pv -> VTvalue pv.pv_ity | LetA ps -> VTarrow ps.ps_aty in
  fprintf fmt "@[<hov 2>val (%a) :@ %a@]" print_lv lv print_type_v vty;
  (* FIXME: forget only generalized regions *)
  match lv with LetA _ -> forget_tvs_regs () | _ -> ()

let print_let_decl fmt { let_sym = lv ; let_expr = e } =
  fprintf fmt "@[<hov 2>let %a =@ %a@]" print_lv lv print_expr e;
  (* FIXME: forget only generalized regions *)
  match lv with LetA _ -> forget_tvs_regs () | _ -> ()

let print_rec_decl lr fst fmt fd =
  print_rec lr fst fmt fd;
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
  | PDrec fdl ->
      print_list_next newline (print_rec_decl (is_letrec fdl)) fmt fdl
  | PDexn  xs -> print_exn_decl fmt xs

(* Print exceptions *)

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | Mlw_ty.BadItyArity ({its_ts = {ts_args = []}} as ts, _) ->
      fprintf fmt "Type symbol %a expects no arguments" print_its ts
  | Mlw_ty.BadItyArity (ts, app_arg) ->
      let i = List.length ts.its_ts.ts_args in
      fprintf fmt "Type symbol %a expects %i argument%s but is applied to %i"
        print_its ts i (if i = 1 then "" else "s") app_arg
  | Mlw_ty.BadRegArity (ts, app_arg) ->
      let i = List.length ts.its_regs in
      fprintf fmt "Type symbol %a expects \
                   %i region argument%s but is applied to %i"
        print_its ts i (if i = 1 then "" else "s") app_arg
  | Mlw_ty.DuplicateRegion r ->
      fprintf fmt "Region %a is used twice" print_reg r
  | Mlw_ty.UnboundRegion r ->
      fprintf fmt "Unbound region %a" print_reg r
  | Mlw_ty.UnboundException xs ->
      fprintf fmt "This function raises %a but does not \
        specify a post-condition for it" print_xs xs
  | Mlw_ty.RegionMismatch (r1,r2,s) ->
      let r1 = Mreg.find_def r1 r1 s.ity_subst_reg in
      fprintf fmt "Region mismatch between %a and %a"
        print_regty r1 print_regty r2
  | Mlw_ty.TypeMismatch (t1,t2,s) ->
      fprintf fmt "Type mismatch between %a and %a"
        (print_ity_node s 0) t1 print_ity t2
  | Mlw_ty.PolymorphicException (id,_ity) ->
      fprintf fmt "Exception %s has a polymorphic type" id.id_string
  | Mlw_ty.MutableException (id,_ity) ->
      fprintf fmt "The type of exception %s has mutable components" id.id_string
  | Mlw_ty.IllegalAlias _reg ->
      fprintf fmt "This application creates an illegal alias"
  | Mlw_ty.IllegalCompar (tv,_ity) ->
      fprintf fmt "This application instantiates \
          a non-opaque type parameter %a with a program type" print_tv tv
  | Mlw_ty.GhostDiverg ->
      fprintf fmt "This ghost expression contains potentially \
        non-terminating loops or function calls"
  | Mlw_expr.RdOnlyPLS _ls ->
      fprintf fmt "Cannot construct or modify values of a private type"
  | Mlw_expr.HiddenPLS pl ->
      fprintf fmt "'%a' is a constructor/field of an abstract type \
        and cannot be used in a program" print_ls pl.pl_ls;
  | Mlw_expr.StaleRegion (_e, id) ->
      fprintf fmt "This expression prohibits further \
        usage of variable %s" id.id_string
  | Mlw_expr.ValueExpected _e ->
      fprintf fmt "This expression is not a first-order value"
  | Mlw_expr.ArrowExpected _e ->
      fprintf fmt "This expression is not a function and cannot be applied"
  | Mlw_expr.Immutable _e ->
      fprintf fmt "Mutable expression expected"
  | Mlw_decl.NonupdatableType ity ->
      fprintf fmt "Cannot update values of type @[%a@]" print_ity ity
  | _ -> raise exn
  end
