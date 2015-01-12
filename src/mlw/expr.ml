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
open Ty
open Term
open Ity

(** {2 Program symbols} *)

type psymbol = {
  ps_name   : ident;
  ps_cty    : cty;
  ps_ghost  : bool;
  ps_logic  : ps_logic;
  ps_mfield : pvsymbol option;
}

and ps_logic =
  | PLnone            (* non-pure symbol *)
  | PLpv of pvsymbol  (* local let-function *)
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
  (fun id cty gh lg mf ->
    let ps = {
      ps_name   = id;
      ps_cty    = cty;
      ps_ghost  = gh;
      ps_logic  = lg;
      ps_mfield = mf;
    } in
    match lg with
    | PLls ls -> Wls.set ls_to_ps ls ps; ps
    | _ -> ps),
  (fun ls -> Wls.find ls_to_ps ls)

type ps_kind =
  | PKnone            (* non-pure symbol *)
  | PKpv of pvsymbol  (* local let-function *)
  | PKlocal           (* new local let-function *)
  | PKfunc of int     (* new top-level let-function or constructor *)
  | PKpred            (* new top-level let-predicate *)
  | PKlemma           (* top-level or local let-lemma *)

let create_psymbol id ?(ghost=false) ?(kind=PKnone) c =
  let check_effects { cty_effect = e } =
    (* TODO/FIXME: prove that we can indeed ignore resets.
      Normally, resets neither consult nor change the
      external state, and do not affect the specification. *)
    if not (eff_is_pure e) then Loc.errorm
      "this function has side effects, it cannot be declared as pure" in
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
        let res = create_vsymbol (id_fresh "result") ty_bool in
        let q = t_iff (t_equ (t_var res) t_bool_true) t in
        cty_add_post c [create_post res q] in
  match kind with
  | PKnone ->
      mk_ps (id_register id) c ghost PLnone None
  | PKlocal ->
      check_effects c; check_reads c;
      let ity = ity_purify c.cty_result in
      let ity = List.fold_right (fun a ity ->
        ity_func (ity_purify a.pv_ity) ity) c.cty_args ity in
      (* When declaring local let-functions, we need to create a
         mapping vsymbol to use in assertions. As vsymbols are not
         generalisable, we have to freeze the type variables (but
         not regions) of the psymbol, and the easiest way to do that
         is to make these type variables appear in c.cty_reads.
         Moreover, we want to maintain the invariant that every
         variable that occurs freely in an assertion comes from
         a pvsymbol. Therefore, we create a pvsymbol whose type
         is a snapshot of the appropriate mapping type, and put
         it into the ps_logic field. This pvsymbol should not be
         used in the program, as it has lost all preconditions,
         which is why we declare it as ghost. In other words,
         this pvsymbol behaves exactly as Epure of its pv_vs. *)
      let v = create_pvsymbol ~ghost:true id ity in
      let t = t_func_app_l (t_var v.pv_vs) (arg_list c) in
      mk_ps v.pv_vs.vs_name (add_post c t) ghost (PLpv v) None
  | PKpv v ->
      check_effects c; check_reads c;
      let ity = ity_purify c.cty_result in
      let ity = List.fold_right (fun a ity ->
        ity_func (ity_purify a.pv_ity) ity) c.cty_args ity in
      ity_equal_check v.pv_ity ity;
      if not v.pv_ghost then invalid_arg "Expr.create_psymbol";
      let t = t_func_app_l (t_var v.pv_vs) (arg_list c) in
      mk_ps (id_register id) (add_post c t) ghost (PLpv v) None
  | PKfunc constr ->
      check_effects c; check_reads c;
      (* we don't really need to check the well-formedness of
         constructor's signature here, the type declaration
         will take care of it *)
      let ls = create_fsymbol id ~constr (arg_type c) (res_type c) in
      let t = t_app ls (arg_list c) ls.ls_value in
      mk_ps ls.ls_name (add_post c t) ghost (PLls ls) None
  | PKpred ->
      check_effects c; check_reads c;
      if not (ity_equal c.cty_result ity_bool) then
        Loc.errorm "this function does not return a boolean value, \
                    it cannot be declared as a pure predicate";
      let ls = create_psymbol id (arg_type c) in
      let f = t_app ls (arg_list c) None in
      mk_ps ls.ls_name (add_post c f) ghost (PLls ls) None
  | PKlemma ->
      check_effects c;
      mk_ps (id_register id) c ghost PLlemma None

let create_mutable_field id s v =
  if not (List.exists (fun u -> pv_equal u v) s.its_mfields) then
    invalid_arg "Expr.create_mutable_field";
  let ity = ity_app s (List.map ity_var s.its_ts.ts_args) s.its_regions in
  let arg = create_pvsymbol (id_fresh "arg") ity in
  let ls = create_fsymbol id [arg.pv_vs.vs_ty] v.pv_vs.vs_ty in
  let res = create_vsymbol (id_fresh "result") v.pv_vs.vs_ty in
  let t = fs_app ls [t_var arg.pv_vs] v.pv_vs.vs_ty in
  let q = create_post res (t_equ (t_var res) t) in
  let c = create_cty [arg] [] [q] Mexn.empty Spv.empty eff_empty v.pv_ity in
  mk_ps ls.ls_name c v.pv_ghost (PLls ls) (Some v)

let ps_of_ls ls =
  let v_args = List.map (fun ty ->
    create_pvsymbol (id_fresh "u") (ity_of_ty ty)) ls.ls_args in
  let t_args = List.map (fun v -> t_var v.pv_vs) v_args in
  let t = t_app ls t_args ls.ls_value in
  let q = match ls.ls_value with
    | Some ty ->
        let res = create_vsymbol (id_fresh "result") ty in
        create_post res (t_equ (t_var res) t)
    | None ->
        let res = create_vsymbol (id_fresh "result") ty_bool in
        create_post res (t_iff (t_equ (t_var res) t_bool_true) t) in
  let ity = ity_of_ty (t_type q) in
  let c = create_cty v_args [] [q] Mexn.empty Spv.empty eff_empty ity in
  mk_ps ls.ls_name c false (PLls ls) None

let ps_kind ps = match ps.ps_logic with
  | PLnone -> PKnone
  | PLpv v -> PKpv v
  | PLls {ls_value = None} -> PKpred
  | PLls {ls_constr = cns} -> PKfunc cns
  | PLlemma -> PKlemma

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

exception ConstructorExpected of psymbol

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
    | PPapp (ps, _) ->
        raise (ConstructorExpected ps)
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

type assign = pvsymbol * psymbol * pvsymbol (* region * field * value *)

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
  | Etrue
  | Efalse
  | Eany

and let_defn = {
  let_sym  : val_decl;
  let_expr : expr;
}

and rec_defn = {
  rec_defn : fun_defn list;
  rec_decr : lsymbol option;
}

and fun_defn = {
  fun_sym  : psymbol; (* exported symbol *)
  fun_rsym : psymbol; (* internal symbol *)
  fun_expr : expr;    (* Efun *)
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

let e_ghost_raises e =
  e.e_ghost && not (Mexn.is_empty e.e_effect.eff_raises)

let e_fold fn acc e = match e.e_node with
  | Evar _ | Esym _ | Econst _ | Eany | Etrue | Efalse
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
  e_ghost  = if ghost && eff.eff_diverg then
    Loc.errorm "This ghost expression contains potentially \
      non-terminating loops or function calls" else ghost;
  e_effect = eff;
  e_label  = Slab.empty;
  e_loc    = None;
}

let e_var pv = mk_expr (Evar pv) (VtyI pv.pv_ity) pv.pv_ghost eff_empty
let e_sym ps = mk_expr (Esym ps) (VtyC ps.ps_cty) ps.ps_ghost eff_empty

let e_const c =
  let ity = match c with
    | Number.ConstInt  _ -> ity_int
    | Number.ConstReal _ -> ity_real in
  mk_expr (Econst c) (VtyI ity) false eff_empty

let e_nat_const n =
  e_const (Number.ConstInt (Number.int_const_dec (string_of_int n)))

(* let definitions *)

let create_let_defn id ?(ghost=false) e =
  let ghost = ghost || e.e_ghost in
  let lv = match e.e_vty with
    | VtyC c -> ValS (create_psymbol id ~ghost ~kind:PKnone c)
    | VtyI i -> ValV (create_pvsymbol id ~ghost i) in
  { let_sym = lv; let_expr = e }

let create_let_defn_pv id ?(ghost=false) e =
  let ghost = ghost || e.e_ghost in
  let pv = create_pvsymbol id ~ghost (ity_of_expr e) in
  { let_sym = ValV pv; let_expr = e }, pv

let create_let_defn_ps id ?(ghost=false) ?(kind=PKnone) e =
  let ghost = ghost || e.e_ghost in
  let cty = match e.e_vty, kind with
    | _, PKfunc n when n > 0 -> invalid_arg "Expr.create_let_defn_ps"
    | VtyI i, (PKfunc _|PKpred) when ity_immutable i ->
        (* the post will be equality to the logic constant *)
        create_cty [] [] [] Mexn.empty Spv.empty eff_empty i
    | VtyI _, (PKfunc _|PKpred) -> Loc.errorm ?loc:e.e_loc
        "this expression is non-pure, it cannot be used as a pure function"
    | VtyI _, (PKnone|PKlocal|PKpv _|PKlemma) -> Loc.errorm ?loc:e.e_loc
        "this expression is first-order, it cannot be used as a function"
    | VtyC c, _ -> c in
  let ps = create_psymbol id ~ghost ~kind cty in
  { let_sym = ValS ps; let_expr = e }, ps

let e_let_raw ({let_expr = d} as ld) e =
  let eff = eff_union d.e_effect e.e_effect in
  let ghost = e.e_ghost || e_ghost_raises d in
  mk_expr (Elet (ld,e)) e.e_vty ghost eff

let e_rec_raw rd e =
  mk_expr (Erec (rd,e)) e.e_vty e.e_ghost e.e_effect

let proxy_label = create_label "proxy_pvsymbol"
let proxy_labels = Slab.singleton proxy_label

let mk_proxy ~ghost e hd = match e.e_node with
  | Evar v when Slab.is_empty e.e_label -> hd, v
  | _ ->
      let id = id_fresh ?loc:e.e_loc ~label:proxy_labels "o" in
      let ld, v = create_let_defn_pv id ~ghost e in
      ld::hd, v

let e_ghost e = mk_expr (Eghost e) e.e_vty true e.e_effect

let e_ghostify e = if not e.e_ghost then e_ghost e else e

(* Elet, Erec, and Eghost are guaranteed to never change
   the type of the underlying expression. Thus, [fn] can
   expect its argument to have the same [e_vty]. However,
   the argument of [fn] may be non-ghost, even though
   the initial argument of [rewind] was ghost.

   TODO/FIXME: this API implements the fully-named scheme
   of binder representation. Therefore, it is *forbidden* to
   use the same binder ident more than once in an expression,
   otherwise exchanging binders in [rewind] may be incorrect.
   One must never reuse the results of [create_let_defn] and
   [create_rec_defn] when constructing expressions. *)
let rec rewind fn ghost d = match d.e_node with
  | (Elet ({let_sym = ValS {ps_ghost = false}}, _)
  |  Elet ({let_sym = ValV {pv_ghost = false}}, _))
    when ghost -> Loc.errorm ?loc:d.e_loc
      "This let-definition must be explicitly marked ghost"
  | Elet (ld, e) ->
      e_label_copy d (e_let_raw ld (rewind fn ghost e))
  | Erec ({rec_defn = dl} as rd, e) ->
      let ngh fd = not fd.fun_sym.ps_ghost in
      if ghost && List.exists ngh dl then Loc.errorm ?loc:d.e_loc
        "%s must be explicitly marked ghost" (if List.length dl > 1 then
        "These recursive definitions" else "This recursive definition");
      e_label_copy d (e_rec_raw rd (rewind fn ghost e))
  | Eghost e ->
      rewind (fun e -> fn (e_label_copy d (e_ghost e))) true e
  | _ -> fn d

let e_let ({let_sym = lv; let_expr = d} as ld) e = match lv with
  | ValS {ps_logic = PLls _} -> invalid_arg "Expr.e_let"
  | ValS {ps_ghost = gh} ->
      rewind (fun d -> e_let_raw {ld with let_expr = d} e) gh d
  | ValV _ -> e_let_raw ld e

let e_rec ({rec_defn = dl} as rd) e =
  List.iter (fun fd -> match fd.fun_sym.ps_logic with
    | PLls _ -> invalid_arg "Expr.e_rec" | _ -> ()) dl;
  e_rec_raw rd e

(* application and assignment *)

let e_app_raw e vl ityl ity =
  let ghost = e.e_ghost and c = cty_of_expr e in
  let ghost, c = cty_apply ~ghost c vl ityl ity in
  let vty, eff = if c.cty_args = [] then
    VtyI c.cty_result, c.cty_effect else
    VtyC c, eff_empty in
  let mk_app e =
    let eff = eff_union e.e_effect eff in
    mk_expr (Eapp (e,vl,c)) vty ghost eff in
  rewind mk_app ghost e

let e_app e el ityl ity =
  let rec down al el = match al, el with
    | {pv_ghost = ghost}::al, e::el ->
        let hd, vl = down al el in
        let hd, v = mk_proxy ~ghost e hd in
        hd, v::vl
    | _, [] -> [], []
    | _ -> invalid_arg "Expr.e_app" (* BadArity? *) in
  let hd, vl = down (cty_of_expr e).cty_args el in
  List.fold_right e_let_raw hd (e_app_raw e vl ityl ity)

let e_assign_raw al =
  let ghost = List.for_all (fun (r,f,v) ->
    r.pv_ghost || f.ps_ghost || v.pv_ghost) al in
  let conv (r,f,v) = match r.pv_ity.ity_node, f.ps_mfield with
    | Ityreg r, Some f -> r, f, v.pv_ity
    | Ityreg {reg_its = s}, None -> Loc.errorm
        "Type constructor %a has no mutable fields named %s"
        Ity.print_its s f.ps_name.id_string
    | _ -> Loc.errorm "Mutable expression expected" in
  let eff = eff_assign eff_empty (List.map conv al) in
  mk_expr (Eassign al) (VtyI ity_unit) ghost eff

let e_assign al =
  let hr, hv, al = List.fold_right (fun (r,f,v) (hr,hv,al) ->
    let ghost = r.e_ghost || f.ps_ghost || v.e_ghost in
    let hv, v = mk_proxy ~ghost v hv in
    let hr, r = mk_proxy ~ghost r hr in
    hr, hv, (r,f,v)::al) al ([],[],[]) in
  (* first pants, THEN your shoes *)
  List.fold_right e_let_raw hr
    (List.fold_right e_let_raw hv (e_assign_raw al))

(* boolean constructors *)

let e_if e0 e1 e2 =
  ity_equal_check (ity_of_expr e0) ity_bool;
  ity_equal_check (ity_of_expr e1) (ity_of_expr e2);
  let gh = e0.e_ghost || e1.e_ghost || e2.e_ghost in
  let eff = eff_union e1.e_effect e2.e_effect in
  let eff = eff_union e0.e_effect eff in
  mk_expr (Eif (e0,e1,e2)) e1.e_vty gh eff

let e_lazy op e1 e2 =
  ity_equal_check (ity_of_expr e1) ity_bool;
  ity_equal_check (ity_of_expr e2) ity_bool;
  let ghost = e1.e_ghost || e2.e_ghost in
  let eff = eff_union e1.e_effect e2.e_effect in
  mk_expr (Elazy (op,e1,e2)) e1.e_vty ghost eff

let e_not e =
  ity_equal_check (ity_of_expr e) ity_bool;
  mk_expr (Enot e) e.e_vty e.e_ghost e.e_effect

let e_true  = mk_expr Etrue  (VtyI ity_bool) false eff_empty
let e_false = mk_expr Efalse (VtyI ity_bool) false eff_empty

(* loops *)

let e_for_raw v ((f,_,t) as bounds) inv e =
  ity_equal_check v.pv_ity ity_int;
  ity_equal_check f.pv_ity ity_int;
  ity_equal_check t.pv_ity ity_int;
  ity_equal_check (ity_of_expr e) ity_unit;
  let ghost = v.pv_ghost || f.pv_ghost || t.pv_ghost || e.e_ghost in
  mk_expr (Efor (v,bounds,inv,e)) e.e_vty ghost e.e_effect

let e_for v ef dir et inv e =
  let ghost = v.pv_ghost || ef.e_ghost || et.e_ghost || e.e_ghost in
  let hd, vt = mk_proxy ~ghost et [] in
  let hd, vf = mk_proxy ~ghost ef hd in
  List.fold_right e_let_raw hd (e_for_raw v (vf,dir,vt) inv e)

let e_while cnd inv vl e =
  ity_equal_check (ity_of_expr cnd) ity_bool;
  ity_equal_check (ity_of_expr e) ity_unit;
  let ghost = cnd.e_ghost || e.e_ghost in
  let eff = eff_union cnd.e_effect e.e_effect in
  let eff = if vl = [] then eff_diverge eff else eff in
  mk_expr (Ewhile (cnd,inv,vl,e)) e.e_vty ghost eff

(* match-with, try-with, raise *)

let e_case ({e_effect = eff} as e) bl =
  let mb, ity = match bl with
    | [(_,d)] -> false, ity_of_expr d
    | (_,d)::_ -> true, ity_of_expr d
    | [] -> invalid_arg "Expr.e_case" in
  List.iter (fun (pp,d) ->
    if e.e_ghost && not pp.pp_ghost then
      Loc.errorm "Non-ghost pattern in a ghost position";
    ity_equal_check (ity_of_expr d) ity;
    ity_equal_check (ity_of_expr e) pp.pp_ity) bl;
  let ghost = e_ghost_raises e || List.exists (fun (_,d) -> d.e_ghost) bl in
  let ghost = ghost || (mb && List.exists (fun (pp,_) -> pp.pp_ghost) bl) in
  let eff = List.fold_left (fun f (_,d) -> eff_union f d.e_effect) eff bl in
  mk_expr (Ecase (e,bl)) (VtyI ity) ghost eff

let e_try e xl =
  List.iter (fun (xs,v,d) ->
    ity_equal_check v.pv_ity xs.xs_ity;
    ity_equal_check (ity_of_expr d) (ity_of_expr e)) xl;
  let ghost = e.e_ghost || List.exists (fun (_,_,d) -> d.e_ghost) xl in
  let eff = List.fold_left (fun f (xs,_,_) -> eff_catch f xs) e.e_effect xl in
  let eff = List.fold_left (fun f (_,_,d) -> eff_union f d.e_effect) eff xl in
  mk_expr (Etry (e,xl)) e.e_vty ghost eff

let e_raise xs e ity =
  ity_equal_check (ity_of_expr e) xs.xs_ity;
  let eff = eff_raise e.e_effect xs in
  mk_expr (Eraise (xs,e)) (VtyI ity) e.e_ghost eff

(* snapshots, assertions, "any" *)

let e_pure t =
  let ity = Opt.fold (fun _ -> ity_of_ty) ity_bool t.t_ty in
  mk_expr (Epure t) (VtyI ity) true eff_empty

let e_assert ak f =
  mk_expr (Eassert (ak, t_prop f)) (VtyI ity_unit) false eff_empty

let e_absurd ity = mk_expr Eabsurd (VtyI ity) false eff_empty

let e_any c = mk_expr Eany (VtyC c) false eff_empty

(* lambda construction *)

let rec e_vars e = match e.e_node with
  | Evar v -> Spv.singleton v
  | Esym s -> s.ps_cty.cty_reads
  | Efun _ | Eany -> (cty_of_expr e).cty_reads
  | Eapp (e,vl,_) -> List.fold_right Spv.add vl (e_vars e)
  | Elet ({let_sym = ValV v; let_expr = d},e)
  | Elet ({let_sym = ValS {ps_logic = PLpv v}; let_expr = d},e) ->
      Spv.union (e_vars d) (Spv.remove v (e_vars e))
  | Elet ({let_sym = ValS _; let_expr = d},e) | Elazy (_,d,e) ->
      Spv.union (e_vars d) (e_vars e)
  | Erec ({rec_defn = dl},e) ->
      let s = List.fold_left (fun s {fun_sym = ps} ->
        Spv.union s ps.ps_cty.cty_reads) (e_vars e) dl in
      List.fold_left (fun s {fun_sym = {ps_logic = l}} ->
        match l with PLpv v -> Spv.remove v s | _ -> s) s dl
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
  | Econst _ | Eabsurd | Etrue | Efalse -> Spv.empty

let pv_mut v mut = if ity_immutable v.pv_ity then mut else Spv.add v mut
let pv_vis v vis = if v.pv_ghost then vis else ity_r_visible vis v.pv_ity

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
  let check_c rst c = check_r rst c.cty_reads in
  let check_e rst e = check_expr gh mut vis rst e in
  let after_e ({e_effect = eff} as e) =
    if Mreg.is_empty eff.eff_resets then rst else
    Mpv.set_union rst (Mpv.mapi_filter (fun {pv_ity = ity} () ->
      if eff_stale_region eff ity then Some e else None) mut) in
  let ghost_c vis c = Mreg.set_inter vis (cty_ghost_writes gh c) in
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
  | Efun _ | Eany -> check_c rst (cty_of_expr e0)
  | Eassign al ->
      List.iter (fun (r,f,v) -> check_v rst r; check_v rst v;
        if not f.ps_ghost && (gh || r.pv_ghost || v.pv_ghost)
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
      List.iter (fun fd -> check_c rst fd.fun_sym.ps_cty) fdl;
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
  | Econst _ | Eabsurd | Etrue | Efalse -> ()

let e_fun args p q xq ({e_effect = eff} as e) =
  let c = create_cty args p q xq (e_vars e) eff (ity_of_expr e) in
  (* TODO/FIXME: detect stale vars in post-conditions? *)
  let mut = Spv.fold pv_mut c.cty_reads Spv.empty in
  let mut = List.fold_right pv_mut c.cty_args mut in
  check_expr false mut (cty_r_visible c) Mpv.empty e;
  mk_expr (Efun e) (VtyC c) e.e_ghost eff_empty

(* recursive definitions *)

let ps_clone ({ps_name = id; ps_ghost = ghost} as s) c =
  create_psymbol (id_clone id) ~ghost ~kind:(ps_kind s) c

let cty_add_variant d varl = let add s (t,_) = t_freepvs s t in
  cty_add_reads (cty_of_expr d) (List.fold_left add Spv.empty varl)

let rec e_ps_subst sm e = e_label_copy e (match e.e_node with
  | Evar _ | Econst _ | Eany | Etrue | Efalse
  | Eassign _ | Eassert _ | Epure _ | Eabsurd -> e
  | Esym s -> e_sym (Mps.find_def s s sm)
  | Efun d ->
      let d = e_ps_subst sm d in let c = cty_of_expr e in
      e_fun c.cty_args c.cty_pre c.cty_post c.cty_xpost d
  | Eapp (d,vl,c) ->
      let d = e_ps_subst sm d in
      let al = List.map (fun v -> v.pv_ity) c.cty_args in
      e_app_raw d vl al c.cty_result
  | Elet ({let_sym = ValV v; let_expr = d} as ld, e) ->
      let d = e_ps_subst sm d in
      ity_equal_check (ity_of_expr d) v.pv_ity;
      if d.e_ghost && not v.pv_ghost then Loc.errorm
        "Expr.create_rec_defn: ghost status mismatch";
      e_let_raw {ld with let_expr = d} (e_ps_subst sm e)
  | Elet ({let_sym = ValS s; let_expr = d},e) ->
      let d = e_ps_subst sm d in
      if d.e_ghost && not s.ps_ghost then Loc.errorm
        "Expr.create_rec_defn: ghost status mismatch";
      let ld, ns = create_let_defn_ps (id_clone s.ps_name)
        ~ghost:s.ps_ghost ~kind:(ps_kind s) d in
      e_let_raw ld (e_ps_subst (Mps.add s ns sm) e)
  | Erec ({rec_defn = fdl; rec_decr = ds},e) ->
      let ndl = List.map (fun fd ->
        fd.fun_rsym, e_ps_subst sm fd.fun_expr) fdl in
      let merge {fun_sym = s; fun_varl = varl} (rs,d) =
        { fun_sym = ps_clone s (cty_add_variant d varl);
          fun_rsym = rs; fun_expr = d; fun_varl = varl } in
      let nfdl = List.map2 merge fdl (rec_fixp ndl) in
      let add m o n = Mps.add o.fun_sym n.fun_sym m in
      let sm = List.fold_left2 add sm fdl nfdl in
      let rd = {rec_defn = nfdl; rec_decr = ds} in
      e_rec rd (e_ps_subst sm e)
  | Eghost e -> e_ghost (e_ps_subst sm e)
  | Enot e -> e_not (e_ps_subst sm e)
  | Eif (c,d,e) -> e_if (e_ps_subst sm c) (e_ps_subst sm d) (e_ps_subst sm e)
  | Elazy (op,d,e) -> e_lazy op (e_ps_subst sm d) (e_ps_subst sm e)
  | Efor (v,b,inv,e) -> e_for_raw v b inv (e_ps_subst sm e)
  | Ewhile (d,inv,vl,e) -> e_while (e_ps_subst sm d) inv vl (e_ps_subst sm e)
  | Eraise (xs,d) -> e_raise xs (e_ps_subst sm d) (ity_of_expr e)
  | Ecase (d,bl) -> e_case (e_ps_subst sm d)
      (List.map (fun (pp,e) -> pp, e_ps_subst sm e) bl)
  | Etry (d,xl) -> e_try (e_ps_subst sm d)
      (List.map (fun (xs,v,e) -> xs, v, e_ps_subst sm e) xl))

and rec_fixp dl =
  let update sm (s,d) =
    let c = cty_of_expr d in
    if d.e_ghost && not s.ps_ghost then Loc.errorm
      "Expr.create_rec_defn: ghost status mismatch";
    let c = if List.length c.cty_pre < List.length s.ps_cty.cty_pre
            then c else cty_add_pre c [List.hd s.ps_cty.cty_pre] in
    if eff_equal c.cty_effect s.ps_cty.cty_effect &&
       Spv.equal c.cty_reads s.ps_cty.cty_reads
    then sm, (s,d)
    else let n = ps_clone s c in Mps.add s n sm, (n,d) in
  let sm, dl = Lists.map_fold_left update Mps.empty dl in
  if Mps.is_empty sm then dl else
  rec_fixp (List.map (fun (s,d) -> s, e_ps_subst sm d) dl)

let create_rec_defn fdl =
  (* check that the variant relations are well-typed *)
  List.iter (fun (_,_,vl,_) -> List.iter (function
    | t, Some rel -> ignore (ps_app rel [t;t])
    | t, None     -> ignore (t_type t)) vl) fdl;
  (* check that the all variants use the same order *)
  let varl1 = match fdl with
    | (_,_,vl,_)::_ -> List.rev vl
    | [] -> invalid_arg "Expr.create_rec_defn" in
  let no_int t = not (ty_equal (t_type t) ty_int) in
  let check_variant (_,_,vl,_) =
    let vl, varl1 = match List.rev vl, varl1 with
      | (t, None)::vl, (t1, None)::varl1
        when no_int t && no_int t1 -> vl, varl1
      | _, _ -> vl, varl1 in
    let res = try List.for_all2 (fun (t1,r1) (t2,r2) ->
        Opt.equal ty_equal t1.t_ty t2.t_ty &&
        Opt.equal ls_equal r1 r2) vl varl1
      with Invalid_argument _ -> false in
    if not res then Loc.errorm
      "All functions in a recursive definition \
        must use the same well-founded order for variant" in
  List.iter check_variant (List.tl fdl);
  (* create the dummy "decrease" predicate symbol *)
  let add_a l (t,_) = t_type t :: l in
  let ds = match varl1 with
    | [] -> None
    | (t,None)::vl when no_int t ->
        let tv = create_tvsymbol (id_fresh "a") in
        let al = List.fold_left add_a [ty_var tv] vl in
        Some (create_lsymbol (id_fresh "DECR") al None)
    | vl ->
        let al = List.fold_left add_a [] vl in
        Some (create_lsymbol (id_fresh "DECR") al None) in
  let start_eff = if varl1 = [] then
    eff_diverge eff_empty else eff_empty in
  (* create the first substitution *)
  let update sm (s,d,varl,_) =
    let c = cty_of_expr d in
    (* check that the type signatures are consistent *)
    let same u v =
      u.pv_ghost = v.pv_ghost && ity_equal u.pv_ity v.pv_ity in
    if (match d.e_node with Efun _ -> false | _ -> true) ||
       not (Lists.equal same s.ps_cty.cty_args c.cty_args) ||
       not (ity_equal s.ps_cty.cty_result c.cty_result) ||
       (d.e_ghost && not s.ps_ghost) || c.cty_args = []
    then invalid_arg "Expr.create_rec_defn";
    (* prepare the extra "decrease" precondition *)
    let pre = match ds with
      | Some ls -> ps_app ls (List.map fst varl) :: c.cty_pre
      | None -> c.cty_pre in
    (* create the clean psymbol *)
    let id = id_clone s.ps_name in
    let c = create_cty c.cty_args pre
      c.cty_post c.cty_xpost Spv.empty start_eff c.cty_result in
    let ns = create_psymbol id ~ghost:s.ps_ghost ~kind:PKnone c in
    Mps.add s ns sm, (ns,d) in
  let sm, dl = Lists.map_fold_left update Mps.empty fdl in
  (* produce the recursive definition *)
  let conv (s,d) = s, e_ps_subst sm d in
  let merge (_,_,varl,kind) (rs,d) =
    let id = id_clone rs.ps_name in
    let c = cty_add_variant d varl in
    let s = create_psymbol id ~kind ~ghost:rs.ps_ghost c in
    { fun_sym = s; fun_rsym = rs; fun_expr = d; fun_varl = varl } in
  let dl = List.map2 merge fdl (rec_fixp (List.map conv dl)) in
  { rec_defn = dl; rec_decr = ds }

(* built-in symbols *)

let ps_bool_true  = ps_of_ls fs_bool_true
let ps_bool_false = ps_of_ls fs_bool_false

let e_bool_true  = e_app (e_sym ps_bool_true)  [] [] ity_bool
let e_bool_false = e_app (e_sym ps_bool_false) [] [] ity_bool

let ps_tuple = Hint.memo 17 (fun n -> ps_of_ls (fs_tuple n))

let is_ps_tuple ps = ps_equal ps (ps_tuple (List.length ps.ps_cty.cty_args))

let e_tuple el =
  let ity = ity_tuple (List.map ity_of_expr el) in
  e_app (e_sym (ps_tuple (List.length el))) el [] ity

let ps_void = ps_tuple 0

let e_void = e_app (e_sym ps_void) [] [] ity_unit

let ps_func_app = ps_of_ls fs_func_app

let e_func_app fn e =
  let c = ps_func_app.ps_cty in
  let mtch isb a e = ity_match isb a.pv_ity (ity_of_expr e) in
  let isb = List.fold_left2 mtch c.cty_freeze c.cty_args [fn;e] in
  e_app (e_sym ps_func_app) [fn;e] [] (ity_full_inst isb c.cty_result)

let e_func_app_l fn el = List.fold_left e_func_app fn el

(* pretty-pringting *)

open Format
open Pretty

let sprinter = create_ident_printer []
  ~sanitizer:(sanitizer char_to_alpha char_to_alnumus)

let id_of_ps s = match s.ps_logic with
  | PLnone | PLlemma -> s.ps_name
  | PLpv v -> v.pv_vs.vs_name
  | PLls s -> s.ls_name

let forget_ps s = match s.ps_logic with
  | PLnone | PLlemma -> forget_id sprinter s.ps_name
  | PLpv v -> forget_pv v
  | PLls _ -> () (* we don't forget top-level symbols *)

let extract_op s =
  let s = s.ps_name.id_string in
  let len = String.length s in
  if len < 7 then None else
  let inf = String.sub s 0 6 in
  if inf = "infix "  then Some (String.sub s 6 (len - 6)) else
  let prf = String.sub s 0 7 in
  if prf = "prefix " then Some (String.sub s 7 (len - 7)) else
  None

let tight_op s = let c = String.sub s 0 1 in c = "!" || c = "?"

let print_ps fmt s =
  if s.ps_name.id_string = "mixfix []" then pp_print_string fmt "([])" else
  if s.ps_name.id_string = "mixfix []<-" then pp_print_string fmt "([]<-)" else
  if s.ps_name.id_string = "mixfix [<-]" then pp_print_string fmt "([<-])" else
  match extract_op s, s.ps_logic with
  | Some s, _ ->
      let s = Str.replace_first (Str.regexp "^\\*.") " \\0" s in
      let s = Str.replace_first (Str.regexp ".\\*$") "\\0 " s in
      fprintf fmt "(%s)" s
  | _, PLnone | _, PLlemma ->
      pp_print_string fmt (id_unique sprinter s.ps_name)
  | _, PLpv v -> print_pv fmt v
  | _, PLls s -> print_ls fmt s

let print_ps_head fmt s = fprintf fmt "%s%s%a%a"
  (if s.ps_ghost then "ghost " else "")
  (match s.ps_logic with
    | PLnone -> ""
    | PLpv _ -> "function "
    | PLls {ls_value = None} -> "predicate "
    | PLls _ -> "function "
    | PLlemma -> "lemma ")
  print_ps s print_id_labels (id_of_ps s)

let print_invariant fmt f =
  fprintf fmt "@\ninvariant@ { %a }" print_term f

let print_variant fmt varl =
  let print_rel fmt = function
    | Some s -> fprintf fmt "@ with %a" print_ls s
    | None -> () in
  let print_var fmt (t, ps) =
    fprintf fmt " %a%a" Pretty.print_term t print_rel ps in
  if varl <> [] then fprintf fmt "@\nvariant@   {%a }@ "
    (Pp.print_list Pp.comma print_var) varl

(* expressions *)

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let print_list_next sep print fmt = function
  | [] -> ()
  | [x] -> print true fmt x
  | x :: r -> print true fmt x; sep fmt ();
      Pp.print_list sep (print false) fmt r

let debug_print_labels = Debug.register_info_flag "print_labels"
  ~desc:"Print@ labels@ of@ identifiers@ and@ expressions."

let debug_print_locs = Debug.register_info_flag "print_locs"
  ~desc:"Print@ locations@ of@ identifiers@ and@ expressions."

let ambig_cty c =
  let sarg = List.fold_left (fun s v ->
    ity_freeze s v.pv_ity) isb_empty c.cty_args in
  let sres = ity_freeze isb_empty c.cty_result in
  not (Mtv.set_submap sres.isb_tv sarg.isb_tv)

let rec print_expr fmt e = print_lexpr 0 fmt e

and print_lexpr pri fmt e =
  let print_elab pri fmt e =
    if Debug.test_flag debug_print_labels && not (Slab.is_empty e.e_label)
    then fprintf fmt (protect_on (pri > 0) "@[<hov 0>%a@ %a@]")
      (Pp.print_iter1 Slab.iter Pp.space print_label) e.e_label
      (print_enode 0) e
    else print_enode pri fmt e in
  let print_eloc pri fmt e =
    if Debug.test_flag debug_print_locs && e.e_loc <> None
    then fprintf fmt (protect_on (pri > 0) "@[<hov 0>%a@ %a@]")
      (Pp.print_option print_loc) e.e_loc (print_elab 0) e
    else print_elab pri fmt e in
  print_eloc pri fmt e

and print_app pri s fmt vl = match extract_op s, vl with
  | _, [] -> print_ps fmt s
  | Some s, [t1] when tight_op s ->
      fprintf fmt (protect_on (pri > 7) "%s%a") s print_pv t1
  | Some s, [t1] ->
      fprintf fmt (protect_on (pri > 4) "%s %a") s print_pv t1
  | Some s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 4) "@[<hov 1>%a %s@ %a@]")
        print_pv t1 s print_pv t2
  | _, [t1;t2] when s.ps_name.id_string = "mixfix []" ->
      fprintf fmt (protect_on (pri > 6) "%a[%a]") print_pv t1 print_pv t2
  | _, [t1;t2;t3] when s.ps_name.id_string = "mixfix [<-]" ->
      fprintf fmt (protect_on (pri > 6) "%a[%a <- %a]")
        print_pv t1 print_pv t2 print_pv t3
  | _, [t1;t2;t3] when s.ps_name.id_string = "mixfix []<-" ->
      fprintf fmt (protect_on (pri > 0) "%a[%a] <- %a")
        print_pv t1 print_pv t2 print_pv t3
  | _, tl ->
      fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a@ %a@]")
        print_ps s (Pp.print_list Pp.space print_pv) tl

and print_enode pri fmt e = match e.e_node with
  | Evar v -> print_pv fmt v
  | Esym s -> print_ps fmt s
  | Efun e1 ->
      let c = cty_of_expr e in
      if c.cty_args = [] then
        fprintf fmt "@[<hov 2>abstract%a@\n%a@]@\nend"
          print_cty_head c print_expr e1
      else
        fprintf fmt "@[<hov 2>fun %a ->@\n%a@]"
          print_cty_head c print_expr e1
  | Eany ->
      fprintf fmt "@[<hov 2>any %a@]" print_cty (cty_of_expr e)
  | Eapp (e,[],_) -> print_lexpr pri fmt e
  | Eapp ({e_node = Esym s},vl,_) when is_ps_tuple s ->
      fprintf fmt "(%a)" (Pp.print_list Pp.comma print_pv) vl
  | Eapp ({e_node = Esym s},[l;r],_) when ps_equal s ps_func_app ->
      fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a %a@]")
        print_pv l print_pv r
  | Eapp ({e_node = Esym s},vl,{cty_args = []; cty_result = ity})
    when ambig_cty s.ps_cty ->
      fprintf fmt (protect_on (pri > 0) "%a:%a")
        (print_app 5 s) vl print_ity ity
  | Eapp ({e_node = Esym s},vl,_) ->
      print_app pri s fmt vl
  | Eapp ({e_vty = VtyC c} as e,vl,{cty_args = []; cty_result = ity})
    when ambig_cty c ->
      fprintf fmt (protect_on (pri > 0) "@[<hov 1>%a@ %a: %a@]")
        (print_lexpr 5) e (Pp.print_list Pp.space print_pv) vl
        print_ity ity
  | Eapp (e,vl,_) ->
      fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a@ %a@]")
        (print_lexpr 5) e (Pp.print_list Pp.space print_pv) vl
  | Econst c -> print_const fmt c
  | Etrue -> pp_print_string fmt "true"
  | Efalse -> pp_print_string fmt "false"
  | Enot e -> fprintf fmt (protect_on (pri > 4) "not %a") (print_lexpr 4) e
  | Elazy (op,e1,e2) ->
      let p,op = match op with Eand -> 3, "&&" | Eor -> 2, "||" in
      fprintf fmt (protect_on (pri > p) "@[<hov 1>%a %s@ %a@]")
        (print_lexpr (p + 1)) e1 op (print_lexpr p) e2
  | Elet ({let_sym = ValV v; let_expr = e1}, e2)
    when v.pv_vs.vs_name.id_string = "_" &&
         (e1.e_ghost || not v.pv_ghost) &&
         ity_equal v.pv_ity ity_unit ->
      fprintf fmt (protect_on (pri > 0) "%a;@\n%a")
        print_expr e1 print_expr e2
  | Elet (ldf, e) ->
      fprintf fmt (protect_on (pri > 0) "%a@ in@\n%a")
        print_let_defn ldf print_expr e;
      begin match ldf.let_sym with
        | ValV v -> forget_pv v
        | ValS s -> forget_ps s end
  | Erec (rdf, e) ->
      fprintf fmt (protect_on (pri > 0) "%a@ in@\n%a")
        print_rec_defn rdf print_expr e;
      List.iter (fun fd -> forget_ps fd.fun_sym) rdf.rec_defn
  | Eif (e0,e1,e2) ->
      fprintf fmt (protect_on (pri > 0) "if %a then %a@ else %a")
        print_expr e0 print_expr e1 print_expr e2
  | Eassign al ->
      let print_left fmt (r,f,_) =
        fprintf fmt "%a.%a" print_pvty r print_ps f in
      let print_right fmt (_,_,v) = print_pv fmt v in
      fprintf fmt (protect_on (pri > 0) "%a <- %a")
        (Pp.print_list Pp.comma print_left) al
        (Pp.print_list Pp.comma print_right) al
  | Ecase (e0,bl) ->
      fprintf fmt "match %a with@\n@[<hov>%a@]@\nend"
        print_expr e0 (Pp.print_list Pp.newline print_branch) bl
  | Ewhile (d,inv,varl,e) ->
      fprintf fmt "@[<hov 2]while %a do%a%a@\n%a@]@\ndone"
        print_expr d print_invariant inv print_variant varl print_expr e
  | Efor (pv,(pvfrom,dir,pvto),inv,e) ->
      fprintf fmt "@[<hov 2>for %a =@ %a@ %s@ %a@ %ado@\n%a@]@\ndone"
        print_pv pv print_pv pvfrom
        (if dir = To then "to" else "downto") print_pv pvto
        print_invariant inv print_expr e
  | Eraise (xs,e) ->
      fprintf fmt "raise (%a %a)" print_xs xs print_expr e
  | Etry (e,bl) ->
      fprintf fmt "try %a with@\n@[<hov>%a@]@\nend"
        print_expr e (Pp.print_list Pp.newline print_xbranch) bl
  | Eabsurd ->
      fprintf fmt "absurd"
  | Eassert (Assert,f) ->
      fprintf fmt "assert { %a }" print_term f
  | Eassert (Assume,f) ->
      fprintf fmt "assume { %a }" print_term f
  | Eassert (Check,f) ->
      fprintf fmt "check { %a }" print_term f
  | Epure t ->
      fprintf fmt "pure { %a }" print_term t
  | Eghost e ->
      fprintf fmt "ghost@ %a" print_expr e

and print_branch fmt ({pp_pat = p},e) =
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_expr e;
  Svs.iter forget_var p.pat_vars

and print_xbranch fmt (xs,v,e) =
  fprintf fmt "@[<hov 4>| %a %a ->@ %a@]" print_xs xs print_pv v print_expr e;
  forget_pv v

and print_let_defn fmt = function
  | {let_sym = ValV v; let_expr = e} ->
      fprintf fmt "@[<hov 2>let %s%a%a =@ %a@]"
        (if v.pv_ghost then "ghost " else "")
        print_pv v print_id_labels v.pv_vs.vs_name
        (print_lexpr 0 (*4*)) e
  | {let_sym = ValS s; let_expr = {e_node = Efun e} as e0} ->
      fprintf fmt "@[<hov 2>let %a@ %a =@\n%a@]"
        print_ps_head s
        print_cty (cty_of_expr e0)
        (print_lexpr 0 (*4*)) e
  | {let_sym = ValS s; let_expr = e} ->
      fprintf fmt "@[<hov 2>let %a =@\n%a@]"
        print_ps_head s
        (print_lexpr 0 (*4*)) e

and print_rec_defn fmt {rec_defn = fdl} =
  print_list_next Pp.newline print_rec_fun fmt fdl

and print_rec_fun fst fmt fd =
  let e = match fd.fun_expr.e_node with
    | Efun e -> e | _ -> assert false in
  fprintf fmt "@[<hov 2>%s %a@ %a%a =@\n%a@]"
    (if fst then "let rec" else "with")
    print_ps_head fd.fun_sym
    print_cty (cty_of_expr fd.fun_expr)
    print_variant fd.fun_varl
    (print_lexpr 0 (*4*)) e

(* exception handling *)

let () = Exn_printer.register (fun fmt e -> match e with
  | ConstructorExpected s ->
      fprintf fmt "Function %a is not a constructor" print_ps s
  | ItyExpected _e ->
      fprintf fmt "This expression is not a first-order value"
  | CtyExpected _e ->
      fprintf fmt "This expression is not a function and cannot be applied"
  | _ -> raise e)
