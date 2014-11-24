(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Term
open Ity

(** {2 Program symbols} *)

type psymbol = {
  ps_name  : ident;
  ps_cty   : cty;
  ps_ghost : bool;
  ps_logic : ps_logic;
}

and ps_logic =
  | PLnone            (* non-pure symbol *)
  | PLvs of vsymbol   (* local let-function *)
  | PLls of lsymbol   (* top-level let-function or let-predicate *)
  | PLlemma           (* top-level or local let-lemma *)

module Psym = MakeMSHW (struct
  type t = psymbol
  let tag ps = ps.ps_name.id_tag
end)

module Sps = Psym.S
module Mps = Psym.M
module Hps = Psym.H
module Wps = Psym.W

let ps_equal : psymbol -> psymbol -> bool = (==)
let ps_hash ps = id_hash ps.ps_name
let ps_compare ps1 ps2 = id_compare ps1.ps_name ps2.ps_name

let mk_ps, restore_ps =
  let ls_to_ps = Wls.create 17 in
  (fun id cty gh lg ->
    let ps = {
      ps_name  = id;
      ps_cty   = cty;
      ps_ghost = gh;
      ps_logic = lg;
    } in
    match lg with
    | PLls ls -> Wls.set ls_to_ps ls ps; ps
    | _ -> ps),
  (fun ls -> Wls.find ls_to_ps ls)

type ps_kind =
  | PKnone            (* non-pure symbol *)
  | PKlocal           (* local let-function *)
  | PKfunc of int     (* top-level let-function or constructor *)
  | PKpred            (* top-level let-predicate *)
  | PKlemma           (* top-level or local let-lemma *)

let create_psymbol id ?(ghost=false) ?(kind=PKnone) c =
  let check_effects { cty_effect = e } =
    (* TODO/FIXME: prove that we can indeed ignore resets.
      Normally, resets neither consult nor change the
      external state, and do not affect the specification. *)
    if not (eff_is_pure e) then Loc.errorm
      "this function is stateful, it cannot be declared as pure" in
  let check_reads { cty_freeze = isb } =
    if not (Mreg.is_empty isb.isb_reg) then Loc.errorm
      "this function is stateful, it cannot be declared as pure" in
  let res_type c = ty_of_ity c.cty_result in
  let arg_type c = List.map (fun a -> a.pv_vs.vs_ty) c.cty_args in
  let arg_list c = List.map (fun a -> t_var a.pv_vs) c.cty_args in
  let add_post c t = match t.t_ty with
    | Some ty ->
        let res = create_vsymbol (id_fresh "result") ty in
        cty_add_post c [create_post res (t_equ (t_var res) t)]
    | None ->
        let res = create_vsymbol (id_fresh "result") Ty.ty_bool in
        let q = t_iff (t_equ (t_var res) t_bool_true) t in
        cty_add_post c [create_post res q] in
  match kind with
  | PKnone ->
      mk_ps (id_register id) c ghost PLnone
  | PKlocal ->
      check_effects c; check_reads c;
      let ity = ity_purify c.cty_result in
      let ity = List.fold_right (fun a ty ->
        ity_func (ity_purify a.pv_ity) ty) c.cty_args ity in
      (* When declaring local let-functions, we need to create a
         mapping vsymbol to use in assertions. As vsymbols are not
         generalisable, we have to freeze the type variables (but
         not regions) of the psymbol, and the easiest way to do that
         is to make these type variables appear in c.cty_reads.
         Moreover, we want to maintain the invariant that every
         variable that occurs freely in an assertion comes from
         a pvsymbol. Therefore, we create a pvsymbol whose type
         is a snapshot of the appropriate mapping type, and put
         its pv_vs into the ps_logic field. This pvsymbol cannot
         be used in the program, as it has lost all preconditions,
         which is why we declare it as ghost. In other words,
         this pvsymbol behaves exactly as Epure of its pv_vs. *)
      let { pv_vs = v } = create_pvsymbol ~ghost:true id ity in
      let t = t_func_app_l (t_var v) (arg_list c) in
      mk_ps v.vs_name (add_post c t) ghost (PLvs v)
  | PKfunc constr ->
      check_effects c; check_reads c;
      (* we don't really need to check the well-formedness of
         constructor's signature here, the type declaration
         will take care of it *)
      let ls = create_fsymbol id ~constr (arg_type c) (res_type c) in
      let t = t_app ls (arg_list c) ls.ls_value in
      mk_ps ls.ls_name (add_post c t) ghost (PLls ls)
  | PKpred ->
      check_effects c; check_reads c;
      if not (ity_equal c.cty_result ity_bool) then
        Loc.errorm "this function does not return a boolean value, \
                    it cannot be declared as a pure predicate";
      let ls = create_psymbol id (arg_type c) in
      let f = t_app ls (arg_list c) None in
      mk_ps ls.ls_name (add_post c f) ghost (PLls ls)
  | PKlemma ->
      check_effects c;
      mk_ps (id_register id) c ghost PLlemma

(** {2 Program patterns} *)

type prog_pattern = {
  pp_pat   : pattern;
  pp_ity   : ity;
  pp_ghost : bool;
}

type pre_pattern =
  | PPwild
  | PPvar of preid
  | PPapp of psymbol * pre_pattern list
  | PPor  of pre_pattern * pre_pattern
  | PPas  of pre_pattern * preid

let create_prog_pattern pp ?(ghost=false) ity =
  let hv = Hstr.create 3 in
  let gh = ref false in
  let find id ghost ity =
    try
      let pv = Hstr.find hv id.pre_name in
      ity_equal_check ity pv.pv_ity;
      if (pv.pv_ghost <> ghost) then invalid_arg "Expr.make_pattern";
      pv
    with Not_found ->
      let pv = create_pvsymbol id ~ghost ity in
      Hstr.add hv id.pre_name pv; pv
  in
  let rec make ghost ity = function
    | PPwild ->
        pat_wild (ty_of_ity ity)
    | PPvar id ->
        pat_var (find id ghost ity).pv_vs
    | PPapp ({ps_logic = PLls ls} as ps, ppl) when ls.ls_constr > 0 ->
        if ghost && ls.ls_constr > 1 then gh := true;
        let sbs = ity_match isb_empty ps.ps_cty.cty_result ity in
        let mtch arg pp =
          let ghost = ghost || arg.pv_ghost in
          make ghost (ity_full_inst sbs arg.pv_ity) pp in
        let ppl = try List.map2 mtch ps.ps_cty.cty_args ppl with
          | Invalid_argument _ ->
              raise (Term.BadArity (ls, List.length ppl)) in
        pat_app ls ppl (ty_of_ity ity)
    | PPapp ({ps_name = {id_string = s}}, _) ->
        Loc.errorm "%s is not a constructor, it cannot be used in a pattern" s
    | PPor (pp1,pp2) ->
        pat_or (make ghost ity pp1) (make ghost ity pp2)
    | PPas (pp,id) ->
        pat_as (make ghost ity pp) (find id ghost ity).pv_vs
  in
  let pat = make ghost ity pp in
  Hstr.fold Mstr.add hv Mstr.empty,
  { pp_pat = pat; pp_ity = ity; pp_ghost = ghost || !gh }

(** {2 Program expressions} *)

type lazy_op = Eand | Eor

type assertion_kind = Assert | Assume | Check

type for_direction = To | DownTo

type for_bounds = pvsymbol * for_direction * pvsymbol

type invariant = term

type variant = term * lsymbol option (** tau * (tau -> tau -> prop) *)

type assign = pvsymbol * pvsymbol * pvsymbol (* region * field * value *)

type vty =
  | VtyI of ity
  | VtyC of cty

type val_decl =
  | ValV of pvsymbol
  | ValS of psymbol

type expr = {
  e_node   : expr_node;
  e_vty    : vty;
  e_ghost  : bool;
  e_effect : effect;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node =
  | Evar    of pvsymbol
  | Esym    of psymbol
  | Econst  of Number.constant
  | Eapp    of expr * pvsymbol list * cty
  | Efun    of expr
  | Elet    of let_defn * expr
  | Erec    of rec_defn * expr
  | Enot    of expr
  | Elazy   of lazy_op * expr * expr
  | Eif     of expr * expr * expr
  | Ecase   of expr * (prog_pattern * expr) list
  | Eassign of assign list
  | Ewhile  of expr * invariant * variant list * expr
  | Efor    of pvsymbol * for_bounds * invariant * expr
  | Etry    of expr * (xsymbol * pvsymbol * expr) list
  | Eraise  of xsymbol * expr
  | Eghost  of expr
  | Eassert of assertion_kind * term
  | Epure   of term
  | Eabsurd
  | Eany

and let_defn = {
  let_sym  : val_decl;
  let_expr : expr;
}

and rec_defn = {
  rec_defn : fun_defn list;
}

and fun_defn = {
  fun_sym  : psymbol;
  fun_expr : expr; (* Efun *)
  fun_varl : variant list;
}

(* basic tools *)

let e_label ?loc l e = { e with e_label = l; e_loc = loc }

let e_label_add l e = { e with e_label = Slab.add l e.e_label }

let e_label_copy { e_label = lab; e_loc = loc } e =
  let lab = Slab.union lab e.e_label in
  let loc = if e.e_loc = None then loc else e.e_loc in
  { e with e_label = lab; e_loc = loc }

exception ItyExpected of expr
exception CtyExpected of expr

let ity_of_expr e = match e.e_vty with
  | VtyI ity -> ity
  | VtyC _ -> Loc.error ?loc:e.e_loc (ItyExpected e)

let cty_of_expr e = match e.e_vty with
  | VtyI _ -> Loc.error ?loc:e.e_loc (CtyExpected e)
  | VtyC cty -> cty

let e_fold fn acc e = match e.e_node with
  | Evar _ | Esym _ | Econst _ | Eany
  | Eassign _ | Eassert _ | Epure _ | Eabsurd -> acc
  | Efun e | Eapp (e,_,_) | Enot e | Eraise (_,e)
  | Efor (_,_,_,e) | Eghost e -> fn acc e
  | Elet (ld,e) -> fn (fn acc ld.let_expr) e
  | Eif (c,d,e) -> fn (fn (fn acc c) d) e
  | Elazy (_,d,e) | Ewhile (d,_,_,e) -> fn (fn acc d) e
  | Erec (r,e) ->
      fn (List.fold_left (fun acc d -> fn acc d.fun_expr) acc r.rec_defn) e
  | Ecase (d,bl) -> List.fold_left (fun acc (_,e) -> fn acc e) (fn acc d) bl
  | Etry (d,xl) -> List.fold_left (fun acc (_,_,e) -> fn acc e) (fn acc d) xl

exception FoundExpr of expr

(* find a minimal sub-expression satisfying [pr] *)
let e_find_minimal pr e =
  let rec find () e = e_fold find () e;
    if pr e then raise (FoundExpr e) in
  try find () e; raise Not_found with FoundExpr e -> e

(* find a sub-expression whose proper effect satisfies [pr] *)
let find_effect pr e =
  let rec find () e = match e.e_node with
    | Eapp (_,_,{cty_args = []; cty_effect = eff})
      when pr eff -> raise (FoundExpr e)
    | Eassign _ when pr e.e_effect -> raise (FoundExpr e)
    | Efun _ -> () (* or call eff_is_empty at each node *)
    | _ -> e_fold find () e in
  try find () e; raise Not_found with FoundExpr e -> e

(* smart constructors *)

let mk_expr node vty ghost eff = {
  e_node   = node;
  e_vty    = vty;
  e_ghost  = ghost;
  e_effect = eff;
  e_label  = Slab.empty;
  e_loc    = None;
}

let e_var pv = mk_expr (Evar pv) (VtyI pv.pv_ity) pv.pv_ghost eff_empty
let e_sym ps = mk_expr (Esym ps) (VtyC ps.ps_cty) ps.ps_ghost eff_empty

let e_const c =
  let ity = match c with
    | Number.ConstInt _ -> ity_int
    | Number.ConstReal _ -> ity_real in
  mk_expr (Econst c) (VtyI ity) false eff_empty

let e_nat_const n =
  e_const (Number.ConstInt (Number.int_const_dec (string_of_int n)))

let create_let_defn id ?(ghost=false) e =
  let ghost = ghost || e.e_ghost in
  let lv = match e.e_vty with
    | VtyC c -> ValS (create_psymbol id ~ghost ~kind:PKnone c)
    | VtyI i -> ValV (create_pvsymbol id ~ghost i) in
  { let_sym = lv; let_expr = e }

let create_let_defn_pv id ?(ghost=false) e =
  let ghost = ghost || e.e_ghost in
  let ity = match e.e_vty with
    | VtyC ({ cty_args = args; cty_result = res } as c) ->
        let error s = Loc.errorm
          "this function %s, it cannot be used as first-order" s in
        if not (Mreg.is_empty c.cty_freeze.isb_reg &&
                eff_is_empty c.cty_effect) then error "is stateful";
        if not (List.for_all (fun a -> ity_immutable a.pv_ity) args &&
                ity_immutable res) then error "is non-pure";
        if not e.e_ghost && List.exists (fun a -> a.pv_ghost) args
          then error "has ghost arguments";
        if c.cty_pre <> [] then error "is partial";
        List.fold_right (fun a i -> ity_func a.pv_ity i) args res
    | VtyI i -> i in
  let pv = create_pvsymbol id ~ghost ity in
  { let_sym = ValV pv; let_expr = e }, pv

let create_let_defn_ps id ?(ghost=false) ?(kind=PKnone) e =
  let ghost = ghost || e.e_ghost in
  let cty = match e.e_vty, kind with
    | _, PKfunc n when n > 0 -> invalid_arg "Expr.create_let_defn_ps"
    | VtyI _, (PKnone|PKlocal|PKlemma) -> Loc.errorm
        "this expression is first-order, it cannot be used as a function"
    | VtyI i, (PKfunc _|PKpred) when ity_immutable i ->
        (* the post will be equality to the logic constant *)
        create_cty [] [] [] Mexn.empty Spv.empty eff_empty i
    | VtyI _, (PKfunc _|PKpred) -> Loc.errorm
        "this expression is non-pure, it cannot be used as a pure function"
    | VtyC c, _ -> c in
  let ps = create_psymbol id ~ghost ~kind cty in
  { let_sym = ValS ps; let_expr = e }, ps

let e_let ({let_sym = lv; let_expr = d} as ld) e = match lv with
  | ValV _ ->
      let eff = eff_union d.e_effect e.e_effect in
      mk_expr (Elet (ld,e)) e.e_vty e.e_ghost eff
  | ValS {ps_logic = PLls _} ->
      invalid_arg "Expr.e_let"
  | ValS s ->
      let rec rewind d = match d.e_node with
        | Efun _ | Eany | Eapp _ ->
            let ld = {let_sym = lv; let_expr = d} in
            let eff = eff_union d.e_effect e.e_effect in
            mk_expr (Elet (ld,e)) e.e_vty e.e_ghost eff
        | Eghost d -> assert s.ps_ghost; rewind d
        | Elet ({let_sym = ValS {ps_ghost = gh}}, _)
        | Elet ({let_sym = ValV {pv_ghost = gh}}, _)
          when s.ps_ghost && not gh -> Loc.errorm ?loc:d.e_loc
            "This let-definition must be explicitly marked ghost"
        | Elet ({let_expr = d} as ld, e) ->
            let e = rewind e in
            let eff = eff_union d.e_effect e.e_effect in
            mk_expr (Elet (ld,e)) e.e_vty e.e_ghost eff
        | Erec ({rec_defn = dl} as rd, e) ->
            let ngh fd = not fd.fun_sym.ps_ghost in
            if s.ps_ghost && List.exists ngh dl then Loc.errorm ?loc:d.e_loc
              "%s must be explicitly marked ghost" (if List.length dl > 1 then
              "These recursive definitions" else "This recursive definition");
            let e = rewind e in
            mk_expr (Erec (rd,e)) e.e_vty e.e_ghost e.e_effect
      in
      rewind d

(* lambda construction *)

let rec e_vars e = match e.e_node with
  | Evar v -> Spv.singleton v
  | Esym s -> s.ps_cty.cty_reads
  | Efun _ | Eany -> (cty_of_expr e).cty_reads
  | Eapp (e,vl,_) -> List.fold_right Spv.add vl (e_vars e)
  | Elet ({let_sym = ValV v; let_expr = d},e) ->
      Spv.union (e_vars d) (Spv.remove v (e_vars e))
  | Elet ({let_sym = ValS {ps_logic = PLvs v}; let_expr = d},e) ->
      Spv.union (e_vars d) (Spv.remove (restore_pv v) (e_vars e))
  | Elet ({let_sym = ValS _; let_expr = d},e) | Elazy (_,d,e) ->
      Spv.union (e_vars d) (e_vars e)
  | Erec ({rec_defn = dl},e) ->
      (* we ignore variants as they appear in the bodies *)
      let s = List.fold_left (fun s {fun_sym = ps} ->
        Spv.union s ps.ps_cty.cty_reads) (e_vars e) dl in
      List.fold_left (fun s {fun_sym = {ps_logic = pl}} ->
        match pl with PLvs v -> Spv.remove (restore_pv v) s | _ -> s) s dl
  | Enot e | Eraise (_,e) | Eghost e -> e_vars e
  | Eassign al ->
      List.fold_left (fun s (r,_,v) -> Spv.add r (Spv.add v s)) Spv.empty al
  | Eif (c,d,e) -> Spv.union (e_vars c) (Spv.union (e_vars d) (e_vars e))
  | Etry (d,xl) -> List.fold_left (fun s (_,v,e) ->
      Spv.union s (Spv.remove v (e_vars e))) (e_vars d) xl
  | Ecase (d,bl) -> List.fold_left (fun s ({pp_pat = p},e) -> Spv.union s
      (Spv.diff (e_vars e) (pvs_of_vss Spv.empty p.pat_vars))) (e_vars d) bl
  | Ewhile (d,inv,vl,e) -> let s = Spv.union (e_vars d) (e_vars e) in
      List.fold_left (fun s (t,_) -> t_freepvs s t) (t_freepvs s inv) vl
  | Efor (v,(f,_,t),inv,e) ->
      Spv.add f (Spv.add t (Spv.remove v (t_freepvs (e_vars e) inv)))
  | Eassert (_,t) | Epure t -> t_freepvs Spv.empty t
  | Econst _ | Eabsurd -> Spv.empty

let pv_mut v mut = if ity_immutable v.pv_ity then mut else Spv.add v mut
let pv_vis v vis = if v.pv_ghost then vis else ity_r_visible vis v.pv_ity

let cty_mut {cty_args = al; cty_reads = r} =
  Spv.fold pv_mut r (List.fold_right pv_mut al Spv.empty)

let cty_vis {cty_args = al; cty_reads = r} =
  Spv.fold pv_vis r (List.fold_right pv_vis al Sreg.empty)

let rec check_expr gh mut vis rst e0 =
  let gh = gh || e0.e_ghost in
  let find_reset v e =
    (find_effect (fun eff -> eff_stale_region eff v.pv_ity) e).e_loc in
  let error_v v e = Loc.errorm ?loc:(find_reset v e) "This expression \
    prohibits further usage of variable %s" v.pv_vs.vs_name.id_string in
  let error_s s v e = Loc.errorm ?loc:(find_reset v e) "This expression \
    prohibits further usage of function %s" s.ps_name.id_string in
  let error_r _r = Loc.errorm ?loc:e0.e_loc "This expression \
    makes a ghost write into a non-ghost location" in
  let check_v rst v = Opt.iter (error_v v) (Mpv.find_opt v rst) in
  let check_r rst r = Mpv.iter error_v (Mpv.set_inter rst r) in
  let check_t rst t = check_r rst (t_freepvs Spv.empty t) in
  let reset_c rst c = Mpv.set_inter rst c.cty_reads in
  let check_e rst e = check_expr gh mut vis rst e in
  let after_e ({e_effect = eff} as e) =
    if Mreg.is_empty eff.eff_resets then rst else
    Mpv.set_union rst (Mpv.mapi_filter (fun {pv_ity = ty} () ->
      if eff_stale_region eff ty then Some e else None) mut) in
  (* A non-ghost application can perform ghost writes into ghost fields
     or into ghost arguments. The former is always safe, but the latter
     is illegal, if we submit a visible region inside a ghost argument.
     A write effect of a computation is ghost whenever the modified region
     is not visible in any non-ghost argument or read dependency. Indeed,
     if there is at least one non-ghost dependency of a computation where
     the modified region is visible, then the write can not be ghost, or
     the computation itself would have been rejected. For this check to
     be correct, Ity.cty_apply does not accept non-ghost pvsymbols for
     ghost arguments. Otherwise, we would put a non-ghost pvsymbol in
     cty_reads and would mistakenly consider the write effect non-ghost. *)
  let ghost_c vis ({cty_effect = {eff_writes = wr}} as c) =
    let wr = Mreg.filter (fun r fs -> r.reg_its.its_private
          || Spv.exists (fun f -> not f.pv_ghost) fs) wr in
    Mreg.set_inter vis (if gh || Mreg.is_empty wr
      then wr else Mreg.set_diff wr (cty_vis c)) in
  match e0.e_node with
  | Evar v -> check_v rst v
  | Esym s -> Mpv.iter (error_s s) (reset_c rst s.ps_cty)
  | Eapp ({e_node = Efun d},[],({cty_args = []} as c)) ->
      let rst = reset_c rst c and gwr = ghost_c vis c in
      if not (Mpv.is_empty rst && Mreg.is_empty gwr) then
      (check_e rst d; Mpv.iter error_v rst; assert false)
  | Eapp (d,l,c) ->
      check_e rst d; List.iter (check_v (after_e d)) l;
      if c.cty_args = [] then Sreg.iter error_r (ghost_c vis c)
  | Efun _ | Eany ->
      Mpv.iter error_v (reset_c rst (cty_of_expr e0))
  | Eassign al ->
      List.iter (fun (r,f,v) -> check_v rst r; check_v rst v;
        if not f.pv_ghost && (gh || r.pv_ghost || v.pv_ghost)
        then match r.pv_ity.ity_node with
          | Ityreg r when Sreg.mem r vis -> error_r r
          | _ -> ()) al
  | Elet ({let_sym = ValV v; let_expr = d},e) ->
      check_expr (gh || v.pv_ghost) mut vis rst d;
      check_expr gh (pv_mut v mut) (pv_vis v vis) (after_e d) e
  | Elet ({let_sym = ValS s; let_expr = d},e) ->
      check_expr (gh || s.ps_ghost) mut vis rst d;
      check_e (after_e d) e
  | Erec ({rec_defn = fdl},e) ->
      List.iter (fun fd -> check_e rst fd.fun_expr) fdl;
      check_e rst e
  | Elazy (_,d,e) ->
      check_e rst d; check_e (after_e d) e
  | Eif (c,d,e) ->
      check_e rst c; let rst = after_e c in
      check_e rst d; check_e rst e
  | Etry (d,xl) ->
      check_e rst d; let rst = after_e d in
      List.iter (fun (_,_,e) -> check_e rst e) xl
  | Ecase (d,bl) ->
      check_e rst d; let rst = after_e d in
      List.iter (fun ({pp_pat = {pat_vars = vss}},e) ->
        let ppv = pvs_of_vss Spv.empty vss in
        check_expr gh (Spv.fold pv_mut ppv mut)
                      (Spv.fold pv_vis ppv vis) rst e) bl
  | Ewhile (d,inv,vl,e) -> let rst = after_e e0 in
      check_t rst inv; check_e rst d; check_e rst e;
      List.iter (fun (t,_) -> check_t rst t) vl
  | Efor (_,_,inv,e) -> let rst = after_e e in
      check_t rst inv; check_e rst e
  | Enot e | Eraise (_,e) | Eghost e -> check_e rst e
  | Eassert (_,t) | Epure t -> check_t rst t
  | Econst _ | Eabsurd -> ()

let e_fun args p q xq ({e_effect = eff} as e) =
  let c = create_cty args p q xq (e_vars e) eff (ity_of_expr e) in
  (* TODO/FIXME: detect stale vars in post-conditions? *)
  check_expr false (cty_mut c) (cty_vis c) Mpv.empty e;
  mk_expr (Efun e) (VtyC c) e.e_ghost eff_empty
