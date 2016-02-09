(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Ident
open Ty
open Term
open Decl
open Ity
open Expr
open Pdecl

(* basic tools *)

let debug = Debug.register_info_flag "vc"
  ~desc:"Print@ details@ of@ verification@ conditions@ generation."

let ls_of_rs s = match s.rs_logic with RLls ls -> ls | _ -> assert false

let new_of_pv {pv_vs = v} = create_vsymbol (id_clone v.vs_name) v.vs_ty

let res_of_ity ity = create_vsymbol (id_fresh "result") (ty_of_ity ity)

let res_of_expr e =
  create_vsymbol (id_fresh ?loc:e.e_loc "result") (ty_of_ity e.e_ity)

let sp_label = Ident.create_label "vc:fast_wp"

(* VCgen environment *)

type vc_env = {
  known_map : Pdecl.known_map;
  ps_int_le : lsymbol;
  ps_int_ge : lsymbol;
  ps_int_lt : lsymbol;
  ps_int_gt : lsymbol;
  fs_int_pl : lsymbol;
  fs_int_mn : lsymbol;
}

let mk_env {Theory.th_export = ns} kn = {
  known_map = kn;
  ps_int_le = Theory.ns_find_ls ns ["infix <="];
  ps_int_ge = Theory.ns_find_ls ns ["infix >="];
  ps_int_lt = Theory.ns_find_ls ns ["infix <"];
  ps_int_gt = Theory.ns_find_ls ns ["infix >"];
  fs_int_pl = Theory.ns_find_ls ns ["infix +"];
  fs_int_mn = Theory.ns_find_ls ns ["infix -"];
}

let mk_env env kn = mk_env (Env.read_theory env ["int"] "Int") kn

(* explanation labels *)

let vc_label e f =
  let loc = if f.t_loc = None then e.e_loc else f.t_loc in
  let lab = Ident.Slab.union e.e_label f.t_label in
  t_label ?loc lab f

let expl_pre       = Ident.create_label "expl:precondition"
let expl_post      = Ident.create_label "expl:postcondition"
let expl_xpost     = Ident.create_label "expl:exceptional postcondition"
let _expl_assume    = Ident.create_label "expl:assumption"
let _expl_assert    = Ident.create_label "expl:assertion"
let _expl_check     = Ident.create_label "expl:check"
let _expl_absurd    = Ident.create_label "expl:unreachable point"
let _expl_type_inv  = Ident.create_label "expl:type invariant"
let _expl_loop_init = Ident.create_label "expl:loop invariant init"
let _expl_loop_keep = Ident.create_label "expl:loop invariant preservation"
let _expl_loopvar   = Ident.create_label "expl:loop variant decrease"
let _expl_variant   = Ident.create_label "expl:variant decrease"

let lab_has_expl = let expl_regexp = Str.regexp "expl:" in
  Slab.exists (fun l -> Str.string_match expl_regexp l.lab_string 0)

let vc_expl lab f =
  let f = if Slab.mem stop_split f.t_label
    then f else t_label_add stop_split f in
  if lab_has_expl f.t_label then f else t_label_add lab f

(* a type is affected if a modified region is reachable from it *)

let ity_affected wr ity = Util.any ity_rch_fold (Mreg.contains wr) ity

let pv_affected wr v = ity_affected wr v.pv_ity

let rec reg_aff_regs wr s reg =
  let q = reg_exp_fold (reg_aff_regs wr) Sreg.empty reg in
  let affect = not (Sreg.is_empty q) || Mreg.mem reg wr in
  Sreg.union s (if affect then Sreg.add reg q else q)

let ity_aff_regs wr s ity = ity_exp_fold (reg_aff_regs wr) s ity

(* express shared region values as "v.f1.f2.f3" when possible *)

let rec explore_paths kn aff mreg t ity =
  if ity.ity_imm then mreg else
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg r when not (Sreg.mem r aff) -> mreg
  | Ityreg ({reg_its = s; reg_args = tl; reg_regs = rl} as r) ->
      let rec height t = match t.t_node with
        (* prefer user variables to proxy variables *)
        | Tvar v when Slab.mem proxy_label v.vs_name.id_label -> 65536
        | Tvar _ -> 0 | Tapp (_,[t]) -> height t + 1
        | _ -> assert false (* shouldn't happen *) in
      let min t o = if height t < height o then t else o in
      let mreg = Mreg.change (fun o -> Some (Opt.fold min t o)) r mreg in
      explore_its kn aff mreg t s tl rl
  | Ityapp (s,tl,rl) -> explore_its kn aff mreg t s tl rl

and explore_its kn aff mreg t s tl rl =
  let isb = its_match_regs s tl rl in
  let follow mreg rs =
    let ity = ity_full_inst isb rs.rs_cty.cty_result in
    let ls = ls_of_rs rs and ty = Some (ty_of_ity ity) in
    explore_paths kn aff mreg (t_app ls [t] ty) ity in
  List.fold_left follow mreg (find_its_defn kn s).itd_fields

let name_regions kn wr mpv =
  let collect o _ aff = ity_aff_regs wr aff o.pv_ity in
  let aff = Mpv.fold collect mpv Sreg.empty in
  let fill o n mreg = explore_paths kn aff mreg (t_var n) o.pv_ity in
  let mreg = Mpv.fold fill mpv Mreg.empty in
  let complete r nm _ = if nm <> None then nm else
    let ty = ty_app r.reg_its.its_ts (List.map ty_of_ity r.reg_args) in
    Some (t_var (create_vsymbol (id_clone r.reg_name) ty)) in
  Mreg.merge complete mreg aff

(* propositional connectives with limited simplification *)

let sp_implies sp wp = match sp.t_node, wp.t_node with
  | Ttrue, _ | _, Ttrue -> wp
  | _, _ -> t_implies sp wp

let sp_or sp1 sp2 = match sp1.t_node, sp2.t_node with
  | Ttrue, _ | _, Tfalse -> sp1
  | _, Ttrue | Tfalse, _ -> sp2
  | _, _ -> t_or sp1 sp2

let sp_and sp1 sp2 = match sp1.t_node, sp2.t_node with
  | Ttrue, _ | _, Tfalse -> sp2
  | _, Ttrue | Tfalse, _ -> sp1
  | _, _ -> t_and sp1 sp2

let can_simp wp = not (Slab.mem stop_split wp.t_label)

let wp_and wp1 wp2 = match wp1.t_node, wp2.t_node with
  | (Ttrue, _ | _, Tfalse) when can_simp wp1 -> wp2
  | (_, Ttrue | Tfalse, _) when can_simp wp2 -> wp1
  | _, _ -> t_and wp1 wp2

let _wp_if c wp1 wp2 = match c.t_node, wp1.t_node, wp2.t_node with
  | Ttrue, _, _  when can_simp wp2 -> wp1
  | Tfalse, _, _ when can_simp wp1 -> wp2
  | Tnot c, Ttrue, _  when can_simp wp1 -> t_implies c wp2
  | _, Ttrue, _  when can_simp wp1 -> t_implies (t_not c) wp2
  | _, _, Ttrue  when can_simp wp2 -> t_implies c wp1
  | _, _, _ -> t_if c wp1 wp2

let wp_forall vl wp = t_forall_close_simp vl [] wp

let wp_let v t wp = t_let_close_simp v t wp

(* produce a rebuilding postcondition after a write effect *)

let cons_t_simp nt t fl =
  if t_equal nt t then fl else t_equ nt t :: fl

let rec havoc kn wr mreg t ity fl =
  if not (ity_affected wr ity) then t, fl else
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg ({reg_its = s} as r) when s.its_nonfree || Mreg.mem r wr ->
      let itd = find_its_defn kn s in
      let isb = its_match_regs s r.reg_args r.reg_regs in
      let wfs = Mreg.find_def Mpv.empty r wr in
      let nt = Mreg.find r mreg in
      let field rs fl =
        if Mpv.mem (Opt.get rs.rs_field) wfs then fl else
        let ity = ity_full_inst isb rs.rs_cty.cty_result in
        let ls = ls_of_rs rs and ty = Some (ty_of_ity ity) in
        let t = t_app ls [t] ty and nt = t_app ls [nt] ty in
        let t, fl = havoc kn wr mreg t ity fl in
        cons_t_simp nt t fl in
      nt, List.fold_right field itd.itd_fields fl
  | Ityreg {reg_its = s; reg_args = tl; reg_regs = rl}
  | Ityapp (s,tl,rl) ->
      let itd = find_its_defn kn s in
      let isb = its_match_regs s tl rl in
      begin match itd.itd_constructors with
      | [{rs_logic = RLls cs}] (* record *)
        when List.length cs.ls_args = List.length itd.itd_fields ->
          let field rs (tl, fl) =
            let ity = ity_full_inst isb rs.rs_cty.cty_result in
            let t = t_app_infer (ls_of_rs rs) [t] in
            let t, fl = havoc kn wr mreg t ity fl in
            t::tl, fl in
          let tl, fl = List.fold_right field itd.itd_fields ([],fl) in
          let t0 = match tl with
            | {t_node = Tapp (_,[t])}::_ -> t | _ -> t_false in
          let triv rs t = match t.t_node with
            | Tapp (s,[t]) -> ls_equal s (ls_of_rs rs) && t_equal t t0
            | _ -> false in
          let t = if List.for_all2 triv itd.itd_fields tl
            then t0 else fs_app cs tl (ty_of_ity ity) in
          t, fl
      | cl ->
          let ty = ty_of_ity ity in
          let branch ({rs_cty = cty} as rs) =
            let cs = ls_of_rs rs in
            let get_ity v = ity_full_inst isb v.pv_ity in
            let ityl = List.map get_ity cty.cty_args in
            let get_pjv {pv_vs = {vs_name = id}} ity =
              create_vsymbol (id_clone id) (ty_of_ity ity) in
            let vl = List.map2 get_pjv cty.cty_args ityl in
            let p = pat_app cs (List.map pat_var vl) ty in
            let field v ity (tl, fl) =
              let t, fl = havoc kn wr mreg (t_var v) ity fl in
              t::tl, fl in
            let tl, fl = List.fold_right2 field vl ityl ([],[]) in
            (p, fs_app cs tl ty), (p, t_and_l fl) in
          let tbl, fbl = List.split (List.map branch cl) in
          let t = t_case_close t tbl and f = t_case_close_simp t fbl in
          t, begin match f.t_node with Ttrue -> fl | _ -> f::fl end
      end

let print_mpv mpv = if Debug.test_flag debug then
  Format.printf "@[vars = %a@]@." (Pp.print_list Pp.space
    (fun fmt (o,n) -> Format.fprintf fmt "(%a -> %a)"
      Ity.print_pv o Pretty.print_vs n)) (Mpv.bindings mpv)

let print_mreg mreg = if Debug.test_flag debug then
  Format.printf "@[regs = %a@]@." (Pp.print_list Pp.space
    (fun fmt (r,t) -> Format.fprintf fmt "(%a -> %a)"
      Ity.print_reg r Pretty.print_term t)) (Mreg.bindings mreg)

let mpv_of_wp cv res wp =
  if Sreg.is_empty cv then Mpv.empty else
  let fvs = t_freevars Mvs.empty wp in
  let add v _ m =
    let v = restore_pv v in
    if pv_affected cv v then
    Mpv.add v (new_of_pv v) m else m in
  Mvs.fold add (Mvs.remove res fvs) Mpv.empty

let advance mpv f =
  let add o n sbs = Mvs.add o.pv_vs (t_var n) sbs in
  t_subst (Mpv.fold add mpv Mvs.empty) f

let vs_dummy = create_vsymbol (id_fresh "dummy") ty_unit

let wp_havoc {known_map = kn} {eff_writes = wr; eff_covers = cv} wp =
  let mpv = mpv_of_wp cv vs_dummy wp in
  if Mpv.is_empty mpv then wp else
  let mreg = name_regions kn cv mpv in
  let () = print_mpv mpv; print_mreg mreg in
  let add _ t fvs = t_freevars fvs t in
  let fvs = Mreg.fold add mreg Mvs.empty in
  let update {pv_vs = o; pv_ity = ity} n wp =
    let t, fl = havoc kn wr mreg (t_var o) ity [] in
    if Mvs.mem n fvs then
      sp_implies (t_and_l (cons_t_simp (t_var n) t fl)) wp
    else wp_let n t (sp_implies (t_and_l fl) wp) in
  let wp = Mpv.fold update mpv (advance mpv wp) in
  wp_forall (Mvs.keys fvs) wp

let step_back wr1 rd2 wr2 mpv =
  if Mreg.is_empty wr1 then Mpv.empty else
  let back o n =
    if not (pv_affected wr1 o) then None else
    if not (pv_affected wr2 o) then Some n else
    Some (new_of_pv o) in
  let add v mpv =
    if not (pv_affected wr1 v) then mpv
    else Mpv.add v (new_of_pv v) mpv in
  Spv.fold add (Mpv.set_diff rd2 mpv) (Mpv.mapi_filter back mpv)

let step_back_expr e1 e2 mpv = step_back e1.e_effect.eff_covers
                   e2.e_effect.eff_reads e2.e_effect.eff_covers mpv

let sp_havoc {known_map = kn} {eff_writes = wr; eff_covers = cv} mpv sp =
  (* FIXME: sp may contain the result as a pvsymbol *)
  if Sreg.is_empty cv then sp else
  let add_rd v _ s = try Spv.add (restore_pv v) s with Not_found -> s in
  let rd = Mvs.fold add_rd (t_freevars Mvs.empty sp) Spv.empty in
  let mpv = step_back cv rd Mreg.empty mpv in
  if Mpv.is_empty mpv then sp else
  let mreg = name_regions kn cv mpv in
  let () = print_mpv mpv; print_mreg mreg in
  let update {pv_vs = o; pv_ity = ity} n sp =
    let t, fl = havoc kn wr mreg (t_var o) ity [] in
    sp_and (t_and_l (cons_t_simp (t_var n) t fl)) sp in
  Mpv.fold update mpv (advance mpv sp)

(* convert user specifications into wp and sp *)

let t_var_or_void v =
  if ty_equal v.vs_ty ty_unit then t_void else t_var v

let wp_of_pre lab pl = t_and_l (List.map (vc_expl lab) pl)

let wp_of_post lab ity = function
  | q::ql ->
      let v, q = open_post q in let t = t_var_or_void v in
      let mk_post q = vc_expl lab (open_post_with t q) in
      v, t_and_l (vc_expl lab q :: List.map mk_post ql)
  | [] ->
      res_of_ity ity, t_true

let rec push_stop lab f = match f.t_node with
  | Tbinop (Tand,g,h) when not (Slab.mem stop_split f.t_label) ->
      t_label_copy f (t_and (push_stop lab g) (push_stop lab h))
  | _ -> vc_expl lab f

let sp_of_pre lab pl = t_and_l (List.map (push_stop lab) pl)

let sp_of_post lab v ql = let t = t_var_or_void v in
  let push q = push_stop lab (open_post_with t q) in
  t_and_l (List.map push ql)

(* combine a postcondition with a precondition *)

let wp_close res sp wp = wp_forall [res] (sp_implies sp wp)

let sp_close res mpv sp wp =
  (* FIXME: sp may contain intermediate let results in pvsymbols *)
  let is_fresh v _ = (* must bind every pure vsymbol in a wp *)
    try ignore (restore_pv v); false with Not_found -> true in
  let fvs = Mvs.filter is_fresh (t_freevars Mvs.empty sp) in
  let fvs = Mpv.fold (fun _ v m -> Mvs.add v 1 m) mpv fvs in
  let vl = res :: List.rev (Mvs.keys (Mvs.remove res fvs)) in
  wp_forall vl (sp_implies sp (advance mpv wp))

(* classical WP / fast WP *)

let vc_label_fast e (ok,ne,ex) =
  vc_label e ok, vc_label e ne, Mexn.map (vc_label e) ex

let bind_oldies c f =
  let sbs = Mpv.fold (fun {pv_vs = o} {pv_vs = v} s ->
    Mvs.add o (t_var v) s) c.cty_oldies Mvs.empty in
  t_subst sbs f

let rec wp_expr env e res q xq = match e.e_node with
  | _ when Slab.mem sp_label e.e_label ->
      let cv = e.e_effect.eff_covers in
      let mpv = mpv_of_wp cv res q in
      let xq = Mexn.set_inter xq e.e_effect.eff_raises in
      let xq = Mexn.map (fun (v,q) -> v, mpv_of_wp cv v q, q) xq in
      let xmpv = Mexn.map (fun (v,mpv,_) -> v,mpv) xq in
      let ok, ne, ex = sp_expr env e res mpv xmpv in
      let xq_merge _ cq q = match cq, q with
        | Some cq, Some (v,mpv,q) -> Some (sp_close v mpv cq q)
        | None, Some (v,mpv,q) -> Some (sp_close v mpv t_true q)
        | _, None -> None in
      let xq = Mexn.merge xq_merge ex xq in
      let q = sp_close res mpv ne q in
      wp_and ok (Mexn.fold (fun _ g f -> t_and f g) xq q)
  | Evar v ->
      t_subst_single res (vc_label e (t_var v.pv_vs)) q
  | Econst c ->
      t_subst_single res (vc_label e (t_const c)) q

  | Eexec ({c_node = Cfun _} as _c) ->
      assert false (* TODO *)
  | Eexec ({c_cty = {cty_args = _::_}} as _c) ->
      assert false (* TODO *)

  | Eexec {c_cty = {cty_args = []} as c} ->
      (* TODO: handle recursive calls *)
      let cq = sp_of_post expl_post res c.cty_post in
      let q = wp_close res cq q in
      let xq_merge _ cq q = match cq, q with
        | Some cq, Some (v,q) ->
            Some (wp_close v (sp_of_post expl_xpost v cq) q)
        | None, Some (v,q) -> Some (wp_forall [v] q)
        | _, None -> None in
      let xq = Mexn.set_inter xq e.e_effect.eff_raises in
      let xq = Mexn.merge xq_merge c.cty_xpost xq in
      let w = Mexn.fold (fun _ g f -> t_and f g) xq q in
      let w = bind_oldies c (wp_havoc env c.cty_effect w) in
      vc_label e (wp_and (wp_of_pre expl_pre c.cty_pre) w)
  | Elet (LDvar (v, e1), e2) (* FIXME: do we need this? *)
    when Slab.mem proxy_label v.pv_vs.vs_name.id_label ->
    (* we push the label down, past the inserted "let" *)
      let q = wp_expr env (e_label_copy e e2) res q xq in
      wp_expr env e1 v.pv_vs q xq
  | Elet (LDvar (v, e1), e2) ->
      let q = wp_expr env e2 res q xq in
      vc_label e (wp_expr env e1 v.pv_vs q xq)
  | Eif (e1, e2, e3) ->
      let v = res_of_expr e1 in
      let test = t_equ (t_var v) t_bool_true in
      (* TODO: how should we handle prop-behind-bool-typed exprs? *)
      (* TODO: handle e_true and e_false, restore /\ and \/ *)
(* FIXME: wrong if e2 or e3 have preconditions depending on test
      let q = if eff_pure e2.e_effect && eff_pure e3.e_effect then
        let u2 = res_of_expr e2 and u3 = res_of_expr e3 in
        let r = t_subst_single res (t_if test (t_var u2) (t_var u3)) q in
        wp_expr env e2 u2 (wp_expr env e3 u3 (t_subst_single res r q) xq) xq
      else
*)
      let q2 = wp_expr env e2 res q xq in
      let q3 = wp_expr env e3 res q xq in
      vc_label e (wp_expr env e1 v (t_if test q2 q3) xq)
  | Ecase (e1, [{pp_pat = {pat_node = Term.Pwild}}, e2]) ->
      let q = wp_expr env e2 res q xq in
      vc_label e (wp_expr env e1 (res_of_expr e1) q xq)
  | Ecase (e1, [{pp_pat = {pat_node = Term.Papp (cs,[])}}, e2])
    when ls_equal cs fs_void ->
      let q = wp_expr env e2 res q xq in
      vc_label e (wp_expr env e1 (res_of_expr e1) q xq)
  | Ecase (e1, bl) ->
      let res = res_of_expr e1 in
      let branch ({pp_pat = pat}, e) =
        t_close_branch pat (wp_expr env e res q xq) in
      let q = t_case (t_var res) (List.map branch bl) in
      vc_label e (wp_expr env e1 res q xq)
  | _ -> assert false (* TODO *)

and sp_expr env e res mpv xmpv = match e.e_node with
  | Evar v ->
      let t = vc_label e (t_var v.pv_vs) in
      t_true, t_equ (t_var res) t, Mexn.empty
  | Econst c ->
      let t = vc_label e (t_const c) in
      t_true, t_equ (t_var res) t, Mexn.empty

  | Eexec ({c_node = Cfun _} as _c) ->
      assert false (* TODO *)
  | Eexec ({c_cty = {cty_args = _::_}} as _c) ->
      assert false (* TODO *)

  | Eexec {c_cty = {cty_args = []} as c} ->
      (* TODO: handle recursive calls *)
      let cq = sp_of_post expl_post res c.cty_post in
      let sp = sp_havoc env c.cty_effect mpv cq in
      let ne = bind_oldies c sp in
      let xq_merge _ cq q = match cq, q with
        | Some cq, Some (v,mpv) ->
            let cq = sp_of_post expl_xpost v cq in
            let sp = sp_havoc env c.cty_effect mpv cq in
            Some (bind_oldies c sp)
        | None, Some (_,mpv) ->
            Some (sp_havoc env c.cty_effect mpv t_true)
        | _, None -> None in
      let xmpv = Mexn.set_inter xmpv e.e_effect.eff_raises in
      let ex = Mexn.merge xq_merge c.cty_xpost xmpv in
      let out = wp_of_pre expl_pre c.cty_pre, ne, ex in
      vc_label_fast e out
(*
  | Elet (LDvar (v, e1), e2) (* FIXME: do we need this? *)
    when Slab.mem proxy_label v.pv_vs.vs_name.id_label ->
    (* we push the label down, past the inserted "let" *)
      let q = wp_expr env (e_label_copy e e2) res q xq in
      wp_expr env e1 v.pv_vs q xq
*)
  | Elet (LDvar (v, e1), e2) ->
      let out = sp_expr env e2 res mpv xmpv in
      let mpv = step_back_expr e1 e2 mpv in
      vc_label_fast e (sp_seq env e1 v.pv_vs mpv xmpv out)
(*
  | Eif (e1, e2, e3) ->
      let v = res_of_expr e1 in
      let test = t_equ (t_var v) t_bool_true in
      (* TODO: how should we handle prop-behind-bool-typed exprs? *)
      (* TODO: handle e_true and e_false, restore /\ and \/ *)
(* FIXME: wrong if e2 or e3 have preconditions depending on test
      let q = if eff_pure e2.e_effect && eff_pure e3.e_effect then
        let u2 = res_of_expr e2 and u3 = res_of_expr e3 in
        let r = t_subst_single res (t_if test (t_var u2) (t_var u3)) q in
        wp_expr env e2 u2 (wp_expr env e3 u3 (t_subst_single res r q) xq) xq
      else
*)
      let q = t_if test (wp_expr env e2 res q xq) (wp_expr env e3 res q xq) in
      vc_label e (wp_expr env e1 v q xq)
*)
  | Ecase (e1, [{pp_pat = {pat_node = Term.Pwild}}, e2]) ->
      let out = sp_expr env e2 res mpv xmpv in
      let mpv = step_back_expr e1 e2 mpv in
      vc_label_fast e (sp_seq env e1 (res_of_expr e1) mpv xmpv out)
  | Ecase (e1, [{pp_pat = {pat_node = Term.Papp (cs,[])}}, e2])
    when ls_equal cs fs_void ->
      let out = sp_expr env e2 res mpv xmpv in
      let mpv = step_back_expr e1 e2 mpv in
      vc_label_fast e (sp_seq env e1 (res_of_expr e1) mpv xmpv out)
(*
  | Ecase (e1, bl) ->
      let res = res_of_expr e1 in
      let branch ({pp_pat = pat}, e) =
        t_close_branch pat (wp_expr env e res q xq) in
      let q = t_case (t_var res) (List.map branch bl) in
      vc_label e (wp_expr env e1 res q xq)
*)
  | _ -> assert false (* TODO *)

and sp_seq env e v mpv xmpv out = match e.e_node with
(* TODO: check mpv wrt partial effects in e1 and e2
   TODO: decide what to do about vc_label
  | Elet (LDvar (u, e1), e2) ->
      let out = sp_seq env e2 v mpv xmpv out in
      let mpv = step_back_expr e1 e2 mpv in
      vc_label_fast e (sp_seq env e1 u mpv xmpv out)
*)
  | _ ->
      let ok2, ne2, ex2 = out in
      let ok1, ne1, ex1 = sp_expr env e v mpv xmpv in
      let ok = wp_and ok1 (sp_close v mpv ne1 ok2) in
      let shift sp = sp_and ne1 (advance mpv sp) in
      let join _ sp1 sp2 = Some (sp_or sp1 sp2) in
      ok, shift ne2, Mexn.union join ex1 (Mexn.map shift ex2)

and vc_fun env c e =
  let p = sp_of_pre expl_pre c.cty_pre in
  let args = List.map (fun pv -> pv.pv_vs) c.cty_args in
(* TODO: let rec with variants
  let env =
    if c.c_letrec = 0 || c.c_variant = [] then env else
    let lab = t_var lab in
    let t_at_lab (t,_) = t_app fs_at [t; lab] t.t_ty in
    let tl = List.map t_at_lab c.c_variant in
    let lrv = Mint.add c.c_letrec tl env.letrec_var in
    { env with letrec_var = lrv } in
*)
  let mk_xq xs xq = wp_of_post expl_xpost xs.xs_ity xq in
  let r,q = wp_of_post expl_post c.cty_result c.cty_post in
  let w = wp_expr env e r q (Mexn.mapi mk_xq c.cty_xpost) in
  wp_forall args (sp_implies p (bind_oldies c w))

let mk_vc_decl id f =
  let {id_string = nm; id_label = label; id_loc = loc} = id in
  let label = if lab_has_expl label then label else
    Slab.add (Ident.create_label ("expl:VC for " ^ nm)) label in
  let pr = create_prsymbol (id_fresh ~label ?loc ("VC " ^ nm)) in
  let f = t_forall_close (Mvs.keys (t_freevars Mvs.empty f)) [] f in
  create_pure_decl (create_prop_decl Pgoal pr f)

let vc env kn d = match d.pd_node with
  | PDlet (LDsym (s, {c_node = Cfun e; c_cty = cty})) ->
      let env = mk_env env kn in
      let f = vc_fun env cty e in
      [mk_vc_decl s.rs_name f]
  | _ -> []

(*
let vc _env kn d = match d.pd_node with
  | PDlet (LDsym (s,{c_cty = {cty_args = al; cty_effect = eff}})) ->
      let add_read ({pv_vs = vs; pv_ity = ity} as v) mpv =
        if ity_r_stale eff.eff_resets eff.eff_covers ity then mpv else
        let id = id_derive (vs.vs_name.id_string ^ "_new") vs.vs_name in
        Mpv.add v (create_vsymbol id vs.vs_ty) mpv in
      let mpv = List.fold_right add_read al Mpv.empty in
      let mpv = Spv.fold add_read eff.eff_reads mpv in
      let f = t_and_simp_l (sp_havoc kn eff mpv) in
      let fvs = Mvs.domain (t_freevars Mvs.empty f) in
      let f = t_forall_close (Svs.elements fvs) [] f in
      let pr = create_prsymbol (id_fresh (s.rs_name.id_string ^ "_havoc")) in
      [create_pure_decl (create_prop_decl Pgoal pr f)]
  | _ -> []
*)
