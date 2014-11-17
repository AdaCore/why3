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
    if not (eff_is_pure e) then
      Loc.errorm "this function has side effects, \
                  it cannot be declared as pure" in
  let check_reads { cty_freeze = isb } =
    if not (Mreg.is_empty isb.isb_reg) then
      Loc.errorm "this function depends on the global state, \
                  it cannot be declared as pure" in
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
      let v = create_pvsymbol ~ghost:true id ity in
      let t = t_func_app_l (t_var v.pv_vs) (arg_list c) in
      mk_ps v.pv_vs.vs_name (add_post c t) ghost (PLvs v.pv_vs)
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
  | Eassign of expr * pvsymbol (*field*) * pvsymbol
  | Ewhile  of expr * invariant * variant list * expr
  | Efor    of pvsymbol * for_bounds * invariant * expr
  | Etry    of expr * (xsymbol * pvsymbol * expr) list
  | Eraise  of xsymbol * expr
  | Eghost  of expr
  | Eassert of assertion_kind * term
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

(* base tools *)

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

let create_let_defn id e =
  let ghost = e.e_ghost in
  let lv = match e.e_vty with
    | VtyI ity -> ValV (create_pvsymbol id ~ghost ity)
    | VtyC cty -> ValS (create_psymbol id ~ghost ~kind:PKnone cty) in
  { let_sym = lv; let_expr = e }

let create_let_defn_pv id e =
  (* let_defn * pvsymbol *)
  assert false

let create_let_defn_ps id ?(kind=PKnone) e = assert false

(*
let create_let_defn_ps id ?(kind=PKnone) e = match e.e_vty, kind with
  | VtyI
  | _, PKfunc n when n > 0 -> invalid_arg "Expr.create_let_defn_ps"
  |
  | _ ->
      let ps = create_psymbol id ~ghost:e.
  (* let_defn * psymbol *)
  assert false
*)
