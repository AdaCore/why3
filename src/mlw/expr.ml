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

open Stdlib
open Ident
open Ty
open Term
open Ity

(** {2 Routine symbols} *)

type rsymbol = {
  rs_name  : ident;
  rs_cty   : cty;
  rs_logic : rs_logic;
  rs_field : pvsymbol option;
}

and rs_logic =
  | RLnone            (* non-pure symbol *)
  | RLpv of pvsymbol  (* local let-function *)
  | RLls of lsymbol   (* top-level let-function or let-predicate *)
  | RLlemma           (* top-level or local let-lemma *)

module Rsym = MakeMSHW (struct
  type t = rsymbol
  let tag rs = rs.rs_name.id_tag
end)

module Srs = Rsym.S
module Mrs = Rsym.M
module Hrs = Rsym.H
module Wrs = Rsym.W

let rs_equal : rsymbol -> rsymbol -> bool = (==)
let rs_hash rs = id_hash rs.rs_name
let rs_compare rs1 rs2 = id_compare rs1.rs_name rs2.rs_name

let mk_rs, restore_rs =
  let ls_to_rs = Wls.create 17 in
  (fun id cty lg mf ->
    let rs = {
      rs_name  = id;
      rs_cty   = cty;
      rs_logic = lg;
      rs_field = mf;
    } in
    match lg with
    | RLls ls -> Wls.set ls_to_rs ls rs; rs
    | _ -> rs),
  (fun ls -> Wls.find ls_to_rs ls)

type rs_kind =
  | RKnone    (* non-pure symbol *)
  | RKlocal   (* local let-function *)
  | RKfunc    (* top-level let-function *)
  | RKpred    (* top-level let-predicate *)
  | RKlemma   (* top-level or local let-lemma *)

let check_effects ?loc c =
  (* TODO/FIXME: prove that we can indeed ignore resets.
     Normally, resets neither consult nor change the
     external state, and do not affect the specification. *)
  if c.cty_effect.eff_oneway then Loc.errorm ?loc
    "This function may not terminate, it cannot be used as pure";
  if not (eff_pure c.cty_effect) then Loc.errorm ?loc
    "This function has side effects, it cannot be used as pure"

let check_reads ?loc c =
  if not (Spv.is_empty (cty_reads c)) then Loc.errorm ?loc
    "This function depends on external variables, it cannot be used as pure"

let check_state ?loc c =
  if not (Mreg.is_empty c.cty_freeze.isb_reg) then Loc.errorm ?loc
    "This function is stateful, it cannot be used as pure"

let cty_ghostify ?loc gh c = try cty_ghostify gh c with
  | BadGhostWrite (v,_) -> Loc.errorm ?loc
      "This ghost function modifies the non-ghost variable %a" print_pv v
  | GhostDivergence -> Loc.errorm ?loc
      "This ghost function may not terminate"

let cty_purify c =
  let add a ity = ity_func (ity_purify a.pv_ity) ity in
  List.fold_right add c.cty_args (ity_purify c.cty_result)

let make_post t = match t.t_ty with
  | Some ty ->
      let res = create_vsymbol (id_fresh "result") ty in
      create_post res (t_equ (t_var res) t)
  | None ->
      let res = create_vsymbol (id_fresh "result") ty_bool in
      create_post res (t_iff (t_equ (t_var res) t_bool_true) t)

let add_post c t = cty_add_post c [make_post t]

let create_rsymbol ({pre_loc=loc} as id) ?(ghost=false) ?(kind=RKnone) c =
  let arg_list c = List.map (fun a -> t_var a.pv_vs) c.cty_args in
  let arg_type c = List.map (fun a -> a.pv_vs.vs_ty) c.cty_args in
  let res_type c = ty_of_ity c.cty_result in
  let c = cty_ghostify ?loc ghost c in
  match kind with
  | RKnone ->
      mk_rs (id_register id) c RLnone None
  | RKlocal ->
      check_effects ?loc c; check_state ?loc c;
      (* When declaring local let-functions, we need to create a
         mapping vsymbol to use in assertions. As vsymbols are not
         generalisable, we have to freeze the type variables (but
         not regions) of the rsymbol, and the easiest way to do that
         is to make these type variables appear in (cty_reads c).
         Moreover, we want to maintain the invariant that every
         variable that occurs freely in an assertion comes from
         a pvsymbol. Therefore, we create a pvsymbol whose type
         is a snapshot of the appropriate mapping type, and put
         it into the rs_logic field. This pvsymbol should not be
         used in the program, as it has lost all preconditions,
         which is why we declare it as ghost. In other words,
         this pvsymbol behaves exactly as Epure of its pv_vs. *)
      let v = create_pvsymbol ~ghost:true id (cty_purify c) in
      let t = t_func_app_l (t_var v.pv_vs) (arg_list c) in
      mk_rs v.pv_vs.vs_name (add_post c t) (RLpv v) None
  | RKfunc ->
      check_effects ?loc c; check_reads ?loc c;
      let ls = create_fsymbol id (arg_type c) (res_type c) in
      let t = t_app ls (arg_list c) ls.ls_value in
      mk_rs ls.ls_name (add_post c t) (RLls ls) None
  | RKpred ->
      check_effects ?loc c; check_reads ?loc c;
      if not (ity_equal c.cty_result ity_bool) then Loc.errorm ?loc
        "This function returns a value of type %a, it cannot be \
          declared as a pure predicate" print_ity c.cty_result;
      let ls = create_psymbol id (arg_type c) in
      let f = t_app ls (arg_list c) None in
      mk_rs ls.ls_name (add_post c f) (RLls ls) None
  | RKlemma ->
      check_effects ?loc c;
      mk_rs (id_register id) c RLlemma None

let rs_dup ({rs_name = {id_loc = loc}} as s) c =
  let id = id_register (id_clone s.rs_name) in
  match s.rs_logic with
  | RLnone ->
      mk_rs id c RLnone None
  | RLpv v ->
      check_effects ?loc c; check_state ?loc c;
      Loc.try2 ?loc ity_equal_check v.pv_ity (cty_purify c);
      let al = List.map (fun a -> t_var a.pv_vs) c.cty_args in
      let t = t_func_app_l (t_var v.pv_vs) al in
      mk_rs id (add_post c t) (RLpv v) None
  | RLls _ ->
      invalid_arg "Expr.rs_dup"
  | RLlemma ->
      check_effects ?loc c;
      mk_rs id c RLlemma None

let create_projection s v =
  let id = id_clone v.pv_vs.vs_name in
  let eff = eff_ghostify v.pv_ghost eff_empty in
  let tyl = List.map ity_var s.its_ts.ts_args in
  let ity = ity_app s tyl s.its_regions in
  let arg = create_pvsymbol (id_fresh "arg") ity in
  let ls = create_fsymbol id [arg.pv_vs.vs_ty] v.pv_vs.vs_ty in
  let q = make_post (fs_app ls [t_var arg.pv_vs] v.pv_vs.vs_ty) in
  let c = create_cty [arg] [] [q] Mexn.empty Mpv.empty eff v.pv_ity in
  mk_rs ls.ls_name c (RLls ls) (Some v)

exception FieldExpected of rsymbol

let mfield_of_rs s = match s.rs_cty.cty_args, s.rs_field with
  | [{pv_ity = {ity_node = Ityreg {reg_its = ts}}}], Some f
    when List.exists (pv_equal f) ts.its_mfields -> f
  | _ -> raise (FieldExpected s)

let create_constructor ~constr id s fl =
  let exn = Invalid_argument "Expr.create_constructor" in
  let fs = List.fold_right (Spv.add_new exn) fl Spv.empty in
  if s.its_privmut || s.its_def <> NoDef then raise exn;
  if s.its_mfields <> [] then begin
    if constr <> 1 then raise exn;
    let mfs = Spv.of_list s.its_mfields in
    if not (Spv.subset mfs fs) then raise exn
  end else if constr < 1 then raise exn;
  let argl = List.map (fun a -> a.pv_vs.vs_ty) fl in
  let tyl = List.map ity_var s.its_ts.ts_args in
  let ity = ity_app s tyl s.its_regions in
  let ty = ty_of_ity ity in
  let ls = create_fsymbol ~constr id argl ty in
  let argl = List.map (fun a -> t_var a.pv_vs) fl in
  let q = make_post (fs_app ls argl ty) in
  let c = create_cty fl [] [q] Mexn.empty Mpv.empty eff_empty ity in
  mk_rs ls.ls_name c (RLls ls) None

let rs_of_ls ls =
  let v_args = List.map (fun ty ->
    create_pvsymbol (id_fresh "u") (ity_of_ty ty)) ls.ls_args in
  let t_args = List.map (fun v -> t_var v.pv_vs) v_args in
  let q = make_post (t_app ls t_args ls.ls_value) in
  let ity = ity_of_ty (t_type q) in
  let c = create_cty v_args [] [q] Mexn.empty Mpv.empty eff_empty ity in
  mk_rs ls.ls_name c (RLls ls) None

let rs_ghost s = s.rs_cty.cty_effect.eff_ghost

(** {2 Program patterns} *)

type prog_pattern = {
  pp_pat   : pattern;
  pp_ity   : ity;
  pp_ghost : bool;
}

type pre_pattern =
  | PPwild
  | PPvar of preid
  | PPapp of rsymbol * pre_pattern list
  | PPor  of pre_pattern * pre_pattern
  | PPas  of pre_pattern * preid

exception ConstructorExpected of rsymbol

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
    | PPapp ({rs_logic = RLls ls} as rs, ppl) when ls.ls_constr > 0 ->
        if ghost && ls.ls_constr > 1 then gh := true;
        let sbs = ity_match isb_empty rs.rs_cty.cty_result ity in
        let mtch arg pp = let ghost = ghost || arg.pv_ghost in
          make ghost (ity_full_inst sbs arg.pv_ity) pp in
        let ppl = try List.map2 mtch rs.rs_cty.cty_args ppl with
          | Invalid_argument _ ->
              raise (Term.BadArity (ls, List.length ppl)) in
        pat_app ls ppl (ty_of_ity ity)
    | PPapp (rs, _) ->
        raise (ConstructorExpected rs)
    | PPor (pp1,pp2) ->
        pat_or (make ghost ity pp1) (make ghost ity pp2)
    | PPas (pp,id) ->
        pat_as (make ghost ity pp) (find id ghost ity).pv_vs
  in
  let pat = make ghost ity pp in
  Hstr.fold Mstr.add hv Mstr.empty,
  { pp_pat = pat; pp_ity = ity; pp_ghost = ghost || !gh }

(** {2 Program expressions} *)

type assertion_kind = Assert | Assume | Check

type for_direction = To | DownTo

type for_bounds = pvsymbol * for_direction * pvsymbol

type invariant = term

type variant = term * lsymbol option (** tau * (tau -> tau -> prop) *)

type assign = pvsymbol * rsymbol * pvsymbol (* region * field * value *)

type expr = {
  e_node   : expr_node;
  e_ity    : ity;
  e_effect : effect;
  e_label  : Slab.t;
  e_loc    : Loc.position option;
}

and expr_node =
  | Evar    of pvsymbol
  | Econst  of Number.constant
  | Eexec   of cexp
  | Eassign of assign list
  | Elet    of let_defn * expr
  | Eif     of expr * expr * expr
  | Ecase   of expr * (prog_pattern * expr) list
  | Ewhile  of expr * invariant list * variant list * expr
  | Efor    of pvsymbol * for_bounds * invariant list * expr
  | Etry    of expr * (xsymbol * pvsymbol * expr) list
  | Eraise  of xsymbol * expr
  | Eassert of assertion_kind * term
  | Epure   of term
  | Eabsurd

and cexp = {
  c_node : cexp_node;
  c_cty  : cty;
}

and cexp_node =
  | Capp of rsymbol * pvsymbol list
  | Cfun of expr
  | Cany

and let_defn =
  | LDvar of pvsymbol * expr
  | LDsym of rsymbol * cexp
  | LDrec of rec_defn list

and rec_defn = {
  rec_sym  : rsymbol; (* exported symbol *)
  rec_rsym : rsymbol; (* internal symbol *)
  rec_fun  : cexp;    (* Cfun *)
  rec_varl : variant list;
}

(* basic tools *)

let e_label ?loc l e = { e with e_label = l; e_loc = loc }

let e_label_add l e = { e with e_label = Slab.add l e.e_label }

let e_label_copy { e_label = lab; e_loc = loc } e =
  let lab = Slab.union lab e.e_label in
  let loc = if e.e_loc = None then loc else e.e_loc in
  { e with e_label = lab; e_loc = loc }

let e_ghost e = e.e_effect.eff_ghost
let c_ghost c = c.c_cty.cty_effect.eff_ghost

(* e_fold never goes under cexps *)
let e_fold fn acc e = match e.e_node with
  | Evar _ | Econst _ | Eexec _ | Eassign _
  | Eassert _ | Epure _ | Eabsurd -> acc
  | Eraise (_,e) | Efor (_,_,_,e)
  | Elet ((LDsym _|LDrec _), e) -> fn acc e
  | Elet (LDvar (_,d), e) | Ewhile (d,_,_,e) -> fn (fn acc d) e
  | Eif (c,d,e) -> fn (fn (fn acc c) d) e
  | Ecase (d,bl) -> List.fold_left (fun acc (_,e) -> fn acc e) (fn acc d) bl
  | Etry (d,xl) -> List.fold_left (fun acc (_,_,e) -> fn acc e) (fn acc d) xl

exception FoundExpr of Loc.position option * expr

(* find a minimal sub-expression whose effect satisfies [pr] *)
let find_effect pr loc e =
  let rec find loc e =
    if not (pr e.e_effect) then loc else
    let loc = if e.e_loc = None then loc else e.e_loc in
    let loc = match e.e_node with
      | Eexec {c_node = Cfun d} -> find loc d
      | _ ->                e_fold find loc e in
    raise (FoundExpr (loc,e)) in
  try find loc e, e with FoundExpr (loc,e) -> loc, e

let e_locate_effect pr e = fst (find_effect pr None e)

(* localize an illegal ghost write *)
let localize_ghost_write v r el =
  let taints eff = Mreg.mem r eff.eff_taints in
  let writes eff = match Mreg.find_opt r eff.eff_writes with
    | Some fds -> r.reg_its.its_privmut ||
        Spv.exists (fun fd -> not fd.pv_ghost) fds
    | None -> false in
  (* check if some component taints region r *)
  List.iter (fun e -> if taints e.e_effect then
    let loc, e = find_effect taints None e in
    let loc, _ = find_effect writes loc e in
    Loc.error ?loc (BadGhostWrite (v,r))) el;
  (* we are ghostified, check if someone writes into r *)
  List.iter (fun e -> if writes e.e_effect then
    let loc = e_locate_effect writes e in
    Loc.error ?loc (BadGhostWrite (v,r))) el;
  raise (BadGhostWrite (v,r))

(* localize a cover effect *)
let localize_cover_stale v r el =
  let covers eff = match Mreg.find_opt r eff.eff_covers with
    | Some cvr -> ity_r_stale r cvr v.pv_ity
    | None -> false in
  List.iter (fun e -> if covers e.e_effect then
    let loc = e_locate_effect covers e in
    Loc.error ?loc (StaleVariable (v,r))) el;
  raise (StaleVariable (v,r))

(* localize a divergence *)
let localize_divergence el =
  let diverges eff = eff.eff_oneway in
  List.iter (fun e -> if diverges e.e_effect then
    let loc = e_locate_effect diverges e in
    Loc.error ?loc GhostDivergence) el;
  raise GhostDivergence

let try_effect el fn x y = try fn x y with
  | BadGhostWrite (v,r) -> localize_ghost_write v r el
  | StaleVariable (v,r) -> localize_cover_stale v r el
  | GhostDivergence     -> localize_divergence el

(* smart constructors *)

let mk_expr node ity eff = {
  e_node   = node;
  e_ity    = ity;
  e_effect = eff;
  e_label  = Slab.empty;
  e_loc    = None;
}

let mk_cexp node cty = {
  c_node   = node;
  c_cty    = cty;
}

let e_var ({pv_ity = ity; pv_ghost = ghost} as v) =
  mk_expr (Evar v) ity (eff_ghostify ghost (eff_read_single v))

let e_const c =
  let ity = match c with
    | Number.ConstInt  _ -> ity_int
    | Number.ConstReal _ -> ity_real in
  mk_expr (Econst c) ity eff_empty

let e_nat_const n =
  assert (n >= 0);
  e_const (Number.const_of_int n)

let e_ghostify gh ({e_effect = eff} as e) =
  if eff.eff_ghost || not gh then e else
  mk_expr e.e_node e.e_ity (try_effect [e] eff_ghostify gh eff)

let c_ghostify gh ({c_cty = cty} as c) =
  if cty.cty_effect.eff_ghost || not gh then c else
  let el = match c.c_node with Cfun e -> [e] | _ -> [] in
  mk_cexp c.c_node (try_effect el (cty_ghostify ?loc:None) gh cty)

(* let-definitions *)

let let_var id ?(ghost=false) e =
  let e = e_ghostify ghost e in
  let v = create_pvsymbol id ~ghost e.e_ity in
  LDvar (v,e), v

let let_sym id ?(ghost=false) ?(kind=RKnone) c =
  let c = c_ghostify ghost c in
  let s = create_rsymbol id ~ghost:(c_ghost c) ~kind c.c_cty in
  LDsym (s,c), s

let e_let ld e =
  let bind_pv v eff = eff_bind_single v eff in
  let bind_rs s eff = match s.rs_logic with
    | RLls _ -> invalid_arg "Expr.e_let"
    | RLpv v -> bind_pv v eff | _ -> eff in
  let bind_rd d eff = bind_rs d.rec_sym eff in
  let eff = match ld with
    | LDvar (v,d) ->
        eff_union_seq d.e_effect (bind_pv v e.e_effect)
    | LDsym (s,c) ->
        eff_read_pre (cty_reads c.c_cty) (bind_rs s e.e_effect)
    | LDrec dl ->
        let e_effect = List.fold_right bind_rd dl e.e_effect in
        (* We do not use the effect of rec_fun, because it does not
           necessarily depend on the external variables in rec_varl.
           We do not use the effect of rec_sym, because it contains
           the RLpv variable when we define a local let-function. *)
        let add s d = Spv.union s (cty_reads d.rec_rsym.rs_cty) in
        eff_read_pre (List.fold_left add Spv.empty dl) e_effect in
  mk_expr (Elet (ld,e)) e.e_ity eff

(* callable expressions *)

let e_exec ({c_cty = cty} as c) = match cty.cty_args with
  | _::_ as al ->
      check_effects cty; check_state cty;
      (* no need to check eff_covers since we are completely pure *)
      if List.exists (fun a -> not a.pv_ity.ity_pure) al ||
        not cty.cty_result.ity_pure then Loc.errorm "This function \
            has mutable type signature, it cannot be used as pure";
      let ghost = List.exists (fun a -> a.pv_ghost) al in
      let effect = eff_bind (Spv.of_list al) cty.cty_effect in
      mk_expr (Eexec c) (cty_purify cty) (eff_ghostify ghost effect)
  | [] ->
      mk_expr (Eexec c) cty.cty_result cty.cty_effect

let c_any c = mk_cexp Cany c

let c_fun args p q xq old ({e_effect = eff} as e) =
  (* reset variables are forbidden in post-conditions *)
  let c = try create_cty args p q xq old eff e.e_ity with
    | BadGhostWrite (v,r) -> localize_ghost_write v r [e]
    | StaleVariable (v,r) -> localize_cover_stale v r [e] in
  mk_cexp (Cfun e) c

let c_app s vl ityl ity =
  mk_cexp (Capp (s,vl)) (cty_apply s.rs_cty vl ityl ity)

let proxy_label = create_label "whyml_proxy_symbol"
let proxy_labels = Slab.singleton proxy_label

let mk_proxy ~ghost e hd = match e.e_node with
  | Evar v when Slab.is_empty e.e_label -> hd, v
  | _ ->
      let id = id_fresh ?loc:e.e_loc ~label:proxy_labels "o" in
      let ld, v = let_var id ~ghost e in
      ld::hd, v

let let_head hd e = List.fold_left (fun e ld -> e_let ld e) e hd

let e_app s el ityl ity =
  let rec args al el = match al, el with
    | {pv_ghost = ghost}::al, e::el ->
        let hd, vl = args al el in
        let hd, v = mk_proxy ~ghost e hd in
        hd, v::vl
    | _, [] -> [], []
    | _ -> invalid_arg "Expr.e_app" in
  let hd, vl = args s.rs_cty.cty_args el in
  let_head hd (e_exec (c_app s vl ityl ity))

type ext_cexp = let_defn list * cexp

let ext_c_sym s = [], mk_cexp (Capp (s,[])) s.rs_cty

let ext_c_app (ldl,c) el ityl ity =
  let ghost = c_ghost c in
  let rec args hd al el = match al, el with
    | {pv_ghost = gh}::al, e::el ->
        let ghost = gh || ghost in
        let hd, v = mk_proxy ~ghost e hd in
        let hd, vl = args hd al el in
        hd, v::vl
    | _, [] -> hd, []
    | _ -> invalid_arg "Expr.ext_c_app" in
  let ldl, vl = args ldl c.c_cty.cty_args el in
  match c.c_node with
    | Capp (s,ul) ->
        ldl, mk_cexp (Capp (s, ul @ vl)) (cty_apply c.c_cty vl ityl ity)
    | Cfun _ | Cany ->
        let ld, s = let_sym (id_fresh ~label:proxy_labels "h") c in
        ldl @ [ld], c_app s vl ityl ity

(* assignment *)

let e_assign_raw al =
  let conv (r,f,v) = r, mfield_of_rs f, v in
  mk_expr (Eassign al) ity_unit (eff_assign (List.map conv al))

let e_assign al =
  let hr, hv, al = List.fold_right (fun (r,f,v) (hr,hv,al) ->
    let ghost = e_ghost r || rs_ghost f || e_ghost v in
    let hv, v = mk_proxy ~ghost v hv in
    let hr, r = mk_proxy ~ghost r hr in
    hr, hv, (r,f,v)::al) al ([],[],[]) in
  (* first pants, THEN your shoes *)
  let_head hv (let_head hr (e_assign_raw al))

(* built-in symbols *)

let rs_true  = rs_of_ls fs_bool_true
let rs_false = rs_of_ls fs_bool_false

let e_true  = e_app rs_true  [] [] ity_bool
let e_false = e_app rs_false [] [] ity_bool

let is_e_true e = match e.e_node with
  | Eexec {c_node = Capp (s,[])} -> rs_equal s rs_true
  | _ -> false

let is_e_false e = match e.e_node with
  | Eexec {c_node = Capp (s,[])} -> rs_equal s rs_false
  | _ -> false

let rs_tuple = Hint.memo 17 (fun n -> rs_of_ls (fs_tuple n))

let is_rs_tuple rs = rs_equal rs (rs_tuple (List.length rs.rs_cty.cty_args))

let e_tuple el =
  let ity = ity_tuple (List.map (fun e -> e.e_ity) el) in
  e_app (rs_tuple (List.length el)) el [] ity

let rs_void = rs_tuple 0

let e_void = e_app rs_void [] [] ity_unit

let is_e_void e = match e.e_node with
  | Eexec {c_node = Capp (s,[])} -> rs_equal s rs_void
  | _ -> false

let rs_func_app = rs_of_ls fs_func_app

let ld_func_app =
  let v_args = rs_func_app.rs_cty.cty_args in
  let ity = rs_func_app.rs_cty.cty_result in
  let c = create_cty v_args [] [] Mexn.empty Mpv.empty eff_empty ity in
  LDsym (rs_func_app, c_any c)

let e_func_app fn e =
  let c = rs_func_app.rs_cty in
  let mtch isb a e = ity_match isb a.pv_ity e.e_ity in
  let isb = List.fold_left2 mtch c.cty_freeze c.cty_args [fn;e] in
  e_app rs_func_app [fn;e] [] (ity_full_inst isb c.cty_result)

let e_func_app_l fn el = List.fold_left e_func_app fn el

(* boolean constructors *)

let e_if e0 e1 e2 =
  ity_equal_check e0.e_ity ity_bool;
  ity_equal_check e1.e_ity e2.e_ity;
  let eff = eff_union_par e1.e_effect e2.e_effect in
  let eff = eff_union_seq e0.e_effect eff in
  let eff = eff_ghostify (e_ghost e0) eff in
  mk_expr (Eif (e0,e1,e2)) e1.e_ity eff

let e_and e1 e2 = e_if e1 e2 e_false
let e_or e1 e2 = e_if e1 e_true e2
let e_not e = e_if e e_false e_true

(* loops *)

let e_for_raw v ((f,_,t) as bounds) inv e =
  ity_equal_check v.pv_ity ity_int;
  ity_equal_check f.pv_ity ity_int;
  ity_equal_check t.pv_ity ity_int;
  ity_equal_check e.e_ity ity_unit;
  let vars = List.fold_left t_freepvs Spv.empty inv in
  let eff = eff_read_pre vars e.e_effect in
  let eff = eff_ghostify (v.pv_ghost || f.pv_ghost || t.pv_ghost) eff in
  ignore (eff_union_seq eff eff); (* check resets *)
  let eff = eff_bind_single v eff in
  let eff = eff_read_single_pre t eff in
  let eff = eff_read_single_pre f eff in
  mk_expr (Efor (v,bounds,inv,e)) e.e_ity eff

let e_for v f dir t inv e =
  let ghost = v.pv_ghost || e_ghost f || e_ghost t || e_ghost e in
  let hd, t = mk_proxy ~ghost t [] in
  let hd, f = mk_proxy ~ghost f hd in
  let_head hd (e_for_raw v (f,dir,t) inv e)

let e_while d inv vl e =
  ity_equal_check d.e_ity ity_bool;
  ity_equal_check e.e_ity ity_unit;
  let vars = List.fold_left (fun s (t,_) -> t_freepvs s t) Spv.empty vl in
  let eff = eff_read_pre (List.fold_left t_freepvs vars inv) e.e_effect in
  let eff = eff_ghostify (e_ghost d) (eff_union_seq d.e_effect eff) in
  let eff = if vl = [] then eff_diverge eff else eff in
  ignore (eff_union_seq eff eff); (* check resets *)
  mk_expr (Ewhile (d,inv,vl,e)) e.e_ity eff

(* match-with, try-with, raise *)

let e_case e bl =
  let ity = match bl with
    | (_,d)::_ -> d.e_ity
    | [] -> invalid_arg "Expr.e_case" in
  List.iter (fun (p,d) ->
    if e_ghost e && not p.pp_ghost then
      Loc.errorm "Non-ghost pattern in a ghost position";
    ity_equal_check d.e_ity ity;
    ity_equal_check e.e_ity p.pp_ity) bl;
  let ghost = List.exists (fun (p,_) -> p.pp_ghost) bl &&
    List.fold_left (fun n (_,d) -> match d.e_node with
      | Eabsurd -> n | _ -> succ n) 0 bl > 1 in
  let eff = List.fold_left (fun eff (p,d) ->
    let pvs = pvs_of_vss Spv.empty p.pp_pat.pat_vars in
    eff_union_par eff (eff_bind pvs d.e_effect)) eff_empty bl in
  let eff = eff_ghostify ghost (eff_union_seq e.e_effect eff) in
  mk_expr (Ecase (e,bl)) ity eff

let e_try e xl =
  List.iter (fun (xs,v,d) ->
    ity_equal_check v.pv_ity xs.xs_ity;
    ity_equal_check d.e_ity e.e_ity) xl;
  let eeff = List.fold_left (fun eff (xs,_,_) ->
    eff_catch eff xs) e.e_effect xl in
  let xeff = List.fold_left (fun eff (_,v,d) ->
    eff_union_par eff (eff_bind_single v d.e_effect)) eff_empty xl in
  let eff = eff_ghostify (e_ghost e) (eff_union_seq eeff xeff) in
  mk_expr (Etry (e,xl)) e.e_ity eff

let e_raise xs e ity =
  ity_equal_check e.e_ity xs.xs_ity;
  mk_expr (Eraise (xs,e)) ity (eff_raise e.e_effect xs)

(* snapshots, assertions, "any" *)

let e_pure t =
  let ity = Opt.fold (fun _ -> ity_of_ty) ity_bool t.t_ty in
  let eff = eff_ghostify true (eff_read (t_freepvs Spv.empty t)) in
  mk_expr (Epure t) ity eff

let e_assert ak f =
  let eff = eff_read (t_freepvs Spv.empty f) in
  mk_expr (Eassert (ak, t_prop f)) ity_unit eff

let e_absurd ity = mk_expr Eabsurd ity eff_empty

(* recursive definitions *)

let cty_add_variant d varl = let add s (t,_) = t_freepvs s t in
  cty_add_reads d.c_cty (List.fold_left add Spv.empty varl)

let rec e_rs_subst sm e =
  e_label_copy e (e_ghostify (e_ghost e) (match e.e_node with
  | Evar _ | Econst _ | Eassign _ | Eassert _ | Epure _ | Eabsurd -> e
  | Eexec c -> e_exec (c_rs_subst sm c)
  | Elet (LDvar (v,d),e) ->
      let d = e_rs_subst sm d in
      ity_equal_check d.e_ity v.pv_ity;
      if e_ghost d <> v.pv_ghost then Loc.errorm
        "Expr.let_rec: ghost status mismatch";
      e_let (LDvar (v,d)) (e_rs_subst sm e)
  | Elet (LDsym (s,d),e) ->
      let d = c_rs_subst sm d in
      if c_ghost d <> rs_ghost s then Loc.errorm
        "Expr.let_rec: ghost status mismatch";
      let ns = rs_dup s d.c_cty in
      e_let (LDsym (ns,d)) (e_rs_subst (Mrs.add s ns sm) e)
  | Elet (LDrec fdl,e) ->
      let ndl = List.map (fun fd ->
        fd.rec_rsym, c_rs_subst sm fd.rec_fun) fdl in
      let merge {rec_sym = s; rec_varl = varl} (rs,d) =
        { rec_sym = rs_dup s (cty_add_variant d varl);
          rec_rsym = rs; rec_fun = d; rec_varl = varl } in
      let nfdl = List.map2 merge fdl (rec_fixp ndl) in
      let add m o n = Mrs.add o.rec_sym n.rec_sym m in
      let sm = List.fold_left2 add sm fdl nfdl in
      e_let (LDrec nfdl) (e_rs_subst sm e)
  | Eif (c,d,e) -> e_if (e_rs_subst sm c) (e_rs_subst sm d) (e_rs_subst sm e)
  | Efor (v,b,inv,e) -> e_for_raw v b inv (e_rs_subst sm e)
  | Ewhile (d,inv,vl,e) -> e_while (e_rs_subst sm d) inv vl (e_rs_subst sm e)
  | Eraise (xs,d) -> e_raise xs (e_rs_subst sm d) e.e_ity
  | Ecase (d,bl) -> e_case (e_rs_subst sm d)
      (List.map (fun (pp,e) -> pp, e_rs_subst sm e) bl)
  | Etry (d,xl) -> e_try (e_rs_subst sm d)
      (List.map (fun (xs,v,e) -> xs, v, e_rs_subst sm e) xl)))

and c_rs_subst sm ({c_node = n; c_cty = c} as d) =
  c_ghostify (cty_ghost c) (match n with
  | Cany -> d
  | Capp (s,vl) ->
      let al = List.map (fun v -> v.pv_ity) c.cty_args in
      c_app (Mrs.find_def s s sm) vl al c.cty_result
  | Cfun e ->
      c_fun c.cty_args c.cty_pre c.cty_post
        c.cty_xpost c.cty_oldies (e_rs_subst sm e))

and rec_fixp dl =
  let update sm (s,({c_cty = c} as d)) =
    if c_ghost d <> rs_ghost s then Loc.errorm
      "Expr.let_rec: ghost status mismatch";
    let c = if List.length c.cty_pre < List.length s.rs_cty.cty_pre
            then c else cty_add_pre [List.hd s.rs_cty.cty_pre] c in
    if eff_equal c.cty_effect s.rs_cty.cty_effect then sm, (s,d)
    else let n = rs_dup s c in Mrs.add s n sm, (n,d) in
  let sm, dl = Lists.map_fold_left update Mrs.empty dl in
  if Mrs.is_empty sm then dl else
  rec_fixp (List.map (fun (s,d) -> s, c_rs_subst sm d) dl)

let let_rec fdl =
  (* check that the variant relations are well-typed *)
  List.iter (fun (_,_,vl,_) -> List.iter (function
    | t, Some rel -> ignore (ps_app rel [t;t])
    | t, None     -> ignore (t_type t)) vl) fdl;
  (* check that the all variants use the same order *)
  let varl1 = match fdl with
    | (_,_,vl,_)::_ -> List.rev vl
    | [] -> invalid_arg "Expr.let_rec" in
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
  let update sm (s,({c_cty = c} as d),varl,_) =
    (* check that the type signatures are consistent *)
    let same u v =
      u.pv_ghost = v.pv_ghost && ity_equal u.pv_ity v.pv_ity in
    if (match d.c_node with Cfun _ -> false | _ -> true) ||
       not (Lists.equal same s.rs_cty.cty_args c.cty_args) ||
       not (ity_equal s.rs_cty.cty_result c.cty_result) ||
       (c_ghost d && not (rs_ghost s)) || c.cty_args = [] ||
       s.rs_logic <> RLnone
    then invalid_arg "Expr.let_rec";
    (* prepare the extra "decrease" precondition *)
    let pre = match ds with
      | Some ls -> ps_app ls (List.map fst varl) :: c.cty_pre
      | None -> c.cty_pre in
    (* create the clean rsymbol *)
    let id = id_clone s.rs_name in
    let c = create_cty c.cty_args pre
      c.cty_post c.cty_xpost c.cty_oldies start_eff c.cty_result in
    let ns = create_rsymbol id ~ghost:(rs_ghost s) ~kind:RKnone c in
    let sm = Mrs.add_new (Invalid_argument "Expr.let_rec") s ns sm in
    sm, (ns, c_ghostify (rs_ghost s) d) in
  let sm, dl = Lists.map_fold_left update Mrs.empty fdl in
  (* produce the recursive definition *)
  let conv (s,d) = s, c_rs_subst sm d in
  let merge (_,_,varl,kind) (rs,d) =
    let id = id_clone rs.rs_name in
    let c = cty_add_variant d varl in
    let s = create_rsymbol id ~kind ~ghost:(rs_ghost rs) c in
    { rec_sym = s; rec_rsym = rs; rec_fun = d; rec_varl = varl } in
  let rdl = List.map2 merge fdl (rec_fixp (List.map conv dl)) in
  LDrec rdl, rdl

let ls_decr_of_let_defn = function
  | LDrec ({rec_rsym = {rs_cty = {cty_pre = {t_node = Tapp (ls,_)}::_}};
            rec_varl = _::_ }::_) -> Some ls
  | _ -> None

(* pretty-pringting *)

open Format
open Pretty

let sprinter = create_ident_printer []
  ~sanitizer:(sanitizer char_to_alpha char_to_alnumus)

let id_of_rs s = match s.rs_logic with
  | RLnone | RLlemma -> s.rs_name
  | RLpv v -> v.pv_vs.vs_name
  | RLls s -> s.ls_name

let forget_rs s = match s.rs_logic with
  | RLnone | RLlemma -> forget_id sprinter s.rs_name
  | RLpv v -> forget_pv v
  | RLls _ -> () (* we don't forget top-level symbols *)

let forget_let_defn = function
  | LDvar (v,_) -> forget_pv v
  | LDsym (s,_) -> forget_rs s
  | LDrec rdl -> List.iter (fun fd -> forget_rs fd.rec_sym) rdl

let extract_op s =
  let s = s.rs_name.id_string in
  let len = String.length s in
  if len < 7 then None else
  let inf = String.sub s 0 6 in
  if inf = "infix "  then Some (String.sub s 6 (len - 6)) else
  let prf = String.sub s 0 7 in
  if prf = "prefix " then Some (String.sub s 7 (len - 7)) else
  None

let tight_op s = let c = String.sub s 0 1 in c = "!" || c = "?"

let print_rs fmt s =
  if s.rs_name.id_string = "mixfix []" then pp_print_string fmt "([])" else
  if s.rs_name.id_string = "mixfix []<-" then pp_print_string fmt "([]<-)" else
  if s.rs_name.id_string = "mixfix [<-]" then pp_print_string fmt "([<-])" else
  match extract_op s, s.rs_logic with
  | Some s, _ ->
      let s = Str.replace_first (Str.regexp "^\\*.") " \\0" s in
      let s = Str.replace_first (Str.regexp ".\\*$") "\\0 " s in
      fprintf fmt "(%s)" s
  | _, RLnone | _, RLlemma ->
      pp_print_string fmt (id_unique sprinter s.rs_name)
  | _, RLpv v -> print_pv fmt v
  | _, RLls s -> print_ls fmt s

let print_rs_head fmt s = fprintf fmt "%s%s%a%a"
  (if s.rs_cty.cty_effect.eff_ghost then "ghost " else "")
  (match s.rs_logic with
    | RLnone -> ""
    | RLpv _ -> "function "
    | RLls {ls_value = None} -> "predicate "
    | RLls _ -> "function "
    | RLlemma -> "lemma ")
  print_rs s print_id_labels (id_of_rs s)

let print_invariant fmt fl =
  let print_inv fmt f = fprintf fmt "@\ninvariant@ { %a }" print_term f in
  Pp.print_list Pp.nothing print_inv fmt fl

let print_variant fmt varl =
  let print_rel fmt = function
    | Some s -> fprintf fmt "@ with %a" print_ls s
    | None -> () in
  let print_var fmt (t,s) =
    fprintf fmt " %a%a" Pretty.print_term t print_rel s in
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

let ht_rs = Hrs.create 7 (* rec_rsym -> rec_sym *)

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

and print_capp pri s fmt vl = match extract_op s, vl with
  | _, [] ->
      print_rs fmt s
  | Some s, [t1] when tight_op s ->
      fprintf fmt (protect_on (pri > 7) "%s%a") s print_pv t1
  | Some s, [t1] ->
      fprintf fmt (protect_on (pri > 4) "%s %a") s print_pv t1
  | Some s, [t1;t2] ->
      fprintf fmt (protect_on (pri > 4) "@[<hov 1>%a %s@ %a@]")
        print_pv t1 s print_pv t2
  | _, [t1;t2] when s.rs_name.id_string = "mixfix []" ->
      fprintf fmt (protect_on (pri > 6) "%a[%a]") print_pv t1 print_pv t2
  | _, [t1;t2;t3] when s.rs_name.id_string = "mixfix [<-]" ->
      fprintf fmt (protect_on (pri > 6) "%a[%a <- %a]")
        print_pv t1 print_pv t2 print_pv t3
  | _, [t1;t2;t3] when s.rs_name.id_string = "mixfix []<-" ->
      fprintf fmt (protect_on (pri > 0) "%a[%a] <- %a")
        print_pv t1 print_pv t2 print_pv t3
  | _, tl ->
      fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a@ %a@]")
        print_rs s (Pp.print_list Pp.space print_pv) tl

and print_cexp exec pri fmt {c_node = n; c_cty = c} = match n with
  | Cany when exec && c.cty_args = [] ->
      fprintf fmt "@[<hov 2>any %a%a@]" print_ity c.cty_result
        (print_spec [] c.cty_pre c.cty_post c.cty_xpost c.cty_effect) None
  | Cany ->
      fprintf fmt "@[<hov 2>any%a@]" print_cty c
  | Cfun e when exec && c.cty_args = [] ->
      fprintf fmt "@[<hov 2>abstract%a@\n%a@]@\nend"
        (print_spec [] c.cty_pre c.cty_post c.cty_xpost eff_empty) None
        print_expr e
  | Cfun e ->
      fprintf fmt "@[<hov 2>fun%a ->@\n%a@]"
        (print_spec c.cty_args c.cty_pre c.cty_post c.cty_xpost eff_empty) None
        print_expr e
  | Capp (s,[]) when rs_equal s rs_true ->
      pp_print_string fmt "true"
  | Capp (s,[]) when rs_equal s rs_false ->
      pp_print_string fmt "false"
  | Capp (s,vl) when is_rs_tuple s ->
      fprintf fmt "(%a)" (Pp.print_list Pp.comma print_pv) vl
  | Capp (s,[l;r]) when rs_equal s rs_func_app ->
      fprintf fmt (protect_on (pri > 5) "@[<hov 1>%a %a@]")
        print_pv l print_pv r
  | Capp (s,vl) when exec && c.cty_args = [] && ambig_cty s.rs_cty ->
      fprintf fmt (protect_on (pri > 0) "%a:%a")
        (print_capp 5 (Hrs.find_def ht_rs s s)) vl print_ity c.cty_result
  | Capp (s,vl) ->
      print_capp pri (Hrs.find_def ht_rs s s) fmt vl

and print_enode pri fmt e = match e.e_node with
  | Evar v -> print_pv fmt v
  | Econst c -> Number.print_constant fmt c
  | Eexec c -> print_cexp true pri fmt c
  | Elet (LDvar (v,e1), e2)
    when v.pv_vs.vs_name.id_string = "_" && ity_equal v.pv_ity ity_unit ->
      fprintf fmt (protect_on (pri > 0) "%s%a;@\n%a")
        (if v.pv_ghost && not (e_ghost e2) then "ghost " else "")
        print_expr e1 print_expr e2
  | Elet (ld, e) ->
      fprintf fmt (protect_on (pri > 0) "%a@ in@\n%a")
        print_let_defn ld print_expr e;
      forget_let_defn ld
  | Eif (e0,e1,e2) when is_e_false e1 && is_e_false e2 ->
      fprintf fmt (protect_on (pri > 4) "not %a") (print_lexpr 4) e0
  | Eif (e0,e1,e2) when is_e_false e2 ->
      fprintf fmt (protect_on (pri > 3) "@[<hov 1>%a &&@ %a@]")
        (print_lexpr 4) e0 (print_lexpr 3) e1
  | Eif (e0,e1,e2) when is_e_true e1 ->
      fprintf fmt (protect_on (pri > 2) "@[<hov 1>%a ||@ %a@]")
        (print_lexpr 3) e0 (print_lexpr 2) e2
  | Eif (e0,e1,e2) ->
      fprintf fmt (protect_on (pri > 0) "if %a then %a@ else %a")
        print_expr e0 print_expr e1 print_expr e2
  | Eassign al ->
      let print_left fmt (r,f,_) =
        fprintf fmt "%a.%a" print_pvty r print_rs f in
      let print_right fmt (_,_,v) = print_pv fmt v in
      fprintf fmt (protect_on (pri > 0) "%a <- %a")
        (Pp.print_list Pp.comma print_left) al
        (Pp.print_list Pp.comma print_right) al
  | Ecase (e0,bl) ->
      (* Elet and Ecase are ghost-containers *)
      let ghost = e_ghost e0 && not (e_ghost e) in
      fprintf fmt "match %s%a%s with@\n@[<hov>%a@]@\nend"
        (if ghost then "ghost (" else "")
        print_expr e0 (if ghost then ")" else "")
        (Pp.print_list Pp.newline print_branch) bl
  | Ewhile (d,inv,varl,e) ->
      fprintf fmt "@[<hov 2]while %a do%a%a@\n%a@]@\ndone"
        print_expr d print_invariant inv print_variant varl print_expr e
  | Efor (pv,(pvfrom,dir,pvto),inv,e) ->
      fprintf fmt "@[<hov 2>for %a =@ %a@ %s@ %a@ %ado@\n%a@]@\ndone"
        print_pv pv print_pv pvfrom
        (if dir = To then "to" else "downto") print_pv pvto
        print_invariant inv print_expr e
  | Eraise (xs,e) when is_e_void e ->
      fprintf fmt "raise %a" print_xs xs
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

and print_branch fmt ({pp_pat = p},e) =
  fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_pat p print_expr e;
  Svs.iter forget_var p.pat_vars

and print_xbranch fmt (xs,v,e) =
  if Spv.mem v e.e_effect.eff_reads then begin
    fprintf fmt "@[<hov 4>| %a %a ->@ %a@]" print_xs xs print_pv v print_expr e;
    forget_pv v
  end else if ity_equal v.pv_ity ity_unit then
    fprintf fmt "@[<hov 4>| %a ->@ %a@]" print_xs xs print_expr e
  else
    fprintf fmt "@[<hov 4>| %a _ ->@ %a@]" print_xs xs print_expr e

and print_let_defn fmt = function
  | LDvar (v,e) ->
      fprintf fmt "@[<hov 2>let %s%a%a =@ %a@]"
        (if v.pv_ghost then "ghost " else "")
        print_pv v print_id_labels v.pv_vs.vs_name
        (print_lexpr 0 (*4*)) e
  | LDsym (s,{c_node = Cfun e; c_cty = c}) ->
      fprintf fmt "@[<hov 2>let %a%a =@\n%a@]"
        print_rs_head s print_cty c
        (print_lexpr 0 (*4*)) e
  | LDsym (s,c) ->
      fprintf fmt "@[<hov 2>let %a =@\n%a@]"
        print_rs_head s
        (print_cexp false 0 (*4*)) c
  | LDrec rdl ->
      List.iter (fun fd -> Hrs.replace ht_rs fd.rec_rsym fd.rec_sym) rdl;
      print_list_next Pp.newline print_rec_fun fmt rdl;
      List.iter (fun fd -> Hrs.remove ht_rs fd.rec_rsym) rdl

and print_rec_fun fst fmt fd =
  let e = match fd.rec_fun.c_node with
    | Cfun e -> e | _ -> assert false in
  fprintf fmt "@[<hov 2>%s %a%a%a =@\n%a@]"
    (if fst then "let rec" else "with")
    print_rs_head fd.rec_sym
    print_cty fd.rec_fun.c_cty
    print_variant fd.rec_varl
    (print_lexpr 0 (*4*)) e

(*
let print_val_decl fmt = function
  | ValV v ->
      fprintf fmt "@[<hov 2>val %s%a%a :@ %a@]"
        (if v.pv_ghost then "ghost " else "")
        print_pv v print_id_labels v.pv_vs.vs_name
        print_ity v.pv_ity
  | ValS ({rs_logic = RLpv v; rs_cty = c} as s) ->
      fprintf fmt "@[<hov 2>val %a%a@]" print_rs_head s
        (print_spec c.cty_args c.cty_pre (List.tl c.cty_post) c.cty_xpost
          (Spv.remove v c.cty_reads) c.cty_effect) (Some c.cty_result)
  | ValS ({rs_logic = RLls _; rs_cty = c} as s) ->
      fprintf fmt "@[<hov 2>val %a%a@]" print_rs_head s
        (print_spec c.cty_args c.cty_pre (List.tl c.cty_post) c.cty_xpost
          c.cty_reads c.cty_effect) (Some c.cty_result)
  | ValS s ->
      fprintf fmt "@[<hov 2>val %a%a@]" print_rs_head s print_cty s.rs_cty
*)

(* exception handling *)

let () = Exn_printer.register (fun fmt e -> match e with
  | ConstructorExpected s -> fprintf fmt
      "Function %a is not a constructor" print_rs s
  | FieldExpected s -> fprintf fmt
      "Function %a is not a mutable field" print_rs s
(*
  | ItyExpected _e -> fprintf fmt
      "This expression is not a first-order value"
  | CtyExpected _e -> fprintf fmt
      "This expression is not a function and cannot be applied"
*)
  | _ -> raise e)
