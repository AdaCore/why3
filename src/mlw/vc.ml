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

let new_of_vs v = create_vsymbol (id_clone v.vs_name) v.vs_ty

let new_of_pv v = new_of_vs v.pv_vs

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

let can_simp wp = match wp.t_node with
  | Ttrue -> not (Slab.mem stop_split wp.t_label)
  | _ -> false

let wp_and wp1 wp2 = match wp1.t_node, wp2.t_node with
  | (Ttrue, _ | _, Tfalse) when can_simp wp1 -> wp2
  | (_, Ttrue | Tfalse, _) when can_simp wp2 -> wp1
  | _, _ -> t_and wp1 wp2

let wp_if c wp1 wp2 = match c.t_node, wp1.t_node, wp2.t_node with
  | Ttrue, _, _  when can_simp wp2 -> wp1
  | Tfalse, _, _ when can_simp wp1 -> wp2
  | Tnot c, Ttrue, _  when can_simp wp1 -> t_implies c wp2
  | _, Ttrue, _  when can_simp wp1 -> t_implies (t_not c) wp2
  | _, _, Ttrue  when can_simp wp2 -> t_implies c wp1
  | _, _, _ -> t_if c wp1 wp2

let wp_case t bl =
  let check b = can_simp (snd (t_open_branch b)) in
  if List.for_all check bl then t_true else t_case t bl

let wp_forall vl wp = t_forall_close_simp vl [] wp

let wp_let v t wp = t_let_close_simp v t wp

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

(* combine postconditions with preconditions *)

let wp_close res sp wp = wp_forall [res] (sp_implies sp wp)

let is_fresh v =
  try ignore (restore_pv v); false with Not_found -> true

let advance mpv f =
  let add o n sbs = Mvs.add o.pv_vs (t_var n) sbs in
  t_subst (Mpv.fold add mpv Mvs.empty) f

let sp_close v mpv sp wp =
  let fvs = t_freevars Mvs.empty sp in
  let fvs = Svs.filter is_fresh (Mvs.domain fvs) in
  let fvs = Mpv.fold (fun _ v s -> Svs.add v s) mpv fvs in
  let fvl = List.rev (Svs.elements (Svs.remove v fvs)) in
  wp_forall (v :: fvl) (sp_implies sp (advance mpv wp))

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

let mpv_of_wp cv wp =
  if Sreg.is_empty cv then Mpv.empty else
  let fvs = t_freevars Mvs.empty wp in
  let add v _ m =
    let v = restore_pv v in
    if pv_affected cv v then
    Mpv.add v (new_of_pv v) m else m in
  Mvs.fold add fvs Mpv.empty

let wp_havoc {known_map = kn} {eff_writes = wr; eff_covers = cv} wp =
  let mpv = mpv_of_wp cv wp in
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

let step_back cv1 rd2 cv2 mpv =
  if Mreg.is_empty cv1 then Mpv.empty else
  let back o n =
    if not (pv_affected cv1 o) then None else
    if not (pv_affected cv2 o) then Some n else
    Some (new_of_pv o) in
  let forth o _ =
    if not (pv_affected cv1 o) then None else
    Some (new_of_pv o) in
  Mpv.set_union (Mpv.mapi_filter back mpv)
    (Mpv.mapi_filter forth (Mpv.set_diff rd2 mpv))

let sp_havoc {known_map = kn} {eff_writes = wr; eff_covers = cv} res sp mpv =
  if Sreg.is_empty cv then sp else
  let rd = t_freepvs Spv.empty (create_post res sp) in
  let mpv = step_back cv rd Mreg.empty mpv in
  if Mpv.is_empty mpv then sp else
  let mreg = name_regions kn cv mpv in
  let () = print_mpv mpv; print_mreg mreg in
  let update {pv_vs = o; pv_ity = ity} n sp =
    let t, fl = havoc kn wr mreg (t_var o) ity [] in
    sp_and (t_and_l (cons_t_simp (t_var n) t fl)) sp in
  Mpv.fold update mpv (advance mpv sp)

let sp_complete {eff_covers = cv} sp mpv =
  let check o n sp =
    if pv_affected cv o then sp else
    sp_and (t_equ (t_var n) (t_var o.pv_vs)) sp in
  Mpv.fold check mpv sp

(* exception-related tools *)

let merge_mexn fn xsp xwp =
  Mexn.inter (fun _ sp wp -> Some (fn sp wp)) xsp xwp

let cty_xpost_real c = (* drop raises {X -> false} *)
  Mexn.set_inter c.cty_xpost c.cty_effect.eff_raises

let mpv_affected {eff_covers = cv} mpv =
  Mpv.filter (fun v _ -> pv_affected cv v) mpv

let xmpv_affected ({eff_raises = rs} as eff) xmpv =
  merge_mexn (fun _ (_,mpv) -> mpv_affected eff mpv) rs xmpv

(* fast-related tools *)

let empty_out = t_true, t_true, Mexn.empty

let out_map fn (ok, ne, ex) = fn ok, fn ne, Mexn.map fn ex

let out_label e out = out_map (vc_label e) out

let out_complete eff (ok, ne, ex) aff xaff =
  let join _ sp mpv = match sp, mpv with
    | Some sp, Some mpv -> Some (sp_complete eff sp mpv)
    | None, Some _ -> Some t_false | _, None -> None in
  ok, sp_complete eff ne aff, Mexn.merge join ex xaff

(* classical WP / fast WP *)

let anon_pat pp = Svs.is_empty pp.pp_pat.pat_vars

let bind_oldies c f =
  let sbs = Mpv.fold (fun {pv_vs = o} {pv_vs = v} s ->
    Mvs.add o (t_var v) s) c.cty_oldies Mvs.empty in
  t_subst sbs f

let rec wp_expr env e res q xq = match e.e_node with
  | _ when Slab.mem sp_label e.e_label ->
      let lab = Slab.remove sp_label e.e_label in
      let e = e_label ?loc:e.e_loc lab e in
      let cv = e.e_effect.eff_covers in
      let reopen res q =
        let q = create_post res q in
        let mpv = mpv_of_wp cv q in
        let res, q = open_post q in
        res, mpv, q in
      let res, mpv, q = reopen res q in
      let xq = merge_mexn (fun (v,q) () ->
        reopen v q) xq e.e_effect.eff_raises in
      let xmpv = Mexn.map (fun (v,mpv,_) -> v,mpv) xq in
      let ok, ne, ex = sp_expr env e res mpv xmpv in
      let xq = merge_mexn (fun cq (v,mpv,q) ->
        sp_close v mpv cq q) ex xq in
      let q = sp_close res mpv ne q in
      wp_and ok (Mexn.fold (fun _ g f -> wp_and f g) xq q)
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
      let join cq (v,q) =
        wp_close v (sp_of_post expl_xpost v cq) q in
      let xq = merge_mexn join (cty_xpost_real c) xq in
      let w = Mexn.fold (fun _ g f -> wp_and f g) xq q in
      let w = bind_oldies c (wp_havoc env c.cty_effect w) in
      vc_label e (wp_and (wp_of_pre expl_pre c.cty_pre) w)
  | Elet (LDvar ({pv_vs = v}, e0), e1) (* FIXME: what for? *)
    when Slab.mem proxy_label v.vs_name.id_label ->
    (* we push the label down, past the inserted "let" *)
      let q = wp_expr env (e_label_copy e e1) res q xq in
      wp_expr env e0 v q xq
  | Elet (LDvar ({pv_vs = v}, e0), e1)
  | Ecase (e0, [{pp_pat = {pat_node = Pvar v}}, e1]) ->
      let q = wp_expr env e1 res q xq in
      vc_label e (wp_expr env e0 v q xq)
  | Ecase (e0, [pp, e1]) when anon_pat pp ->
      let q = wp_expr env e1 res q xq in
      vc_label e (wp_expr env e0 (res_of_expr e0) q xq)
  | Eif (e0, e1, e2) ->
      let v = res_of_expr e0 in
      let test = t_equ (t_var v) t_bool_true in
      (* TODO: how should we handle prop-behind-bool-typed exprs? *)
      (* TODO: handle e_true and e_false, restore /\ and \/ *)
(* FIXME: wrong if e1 or e2 have preconditions depending on test
      let q = if eff_pure e1.e_effect && eff_pure e2.e_effect then
        let u1 = res_of_expr e1 and u2 = res_of_expr e2 in
        let r = t_subst_single res (t_if test (t_var u1) (t_var u2)) q in
        wp_expr env e1 u1 (wp_expr env e2 u2 (t_subst_single res r q) xq) xq
      else
*)
      let q1 = wp_expr env e1 res q xq in
      let q2 = wp_expr env e2 res q xq in
      vc_label e (wp_expr env e0 v (wp_if test q1 q2) xq)
  | Ecase (e0, bl) ->
      let v = res_of_expr e0 in
      let branch ({pp_pat = pat}, e) =
        t_close_branch pat (wp_expr env e res q xq) in
      let q = wp_case (t_var v) (List.map branch bl) in
      vc_label e (wp_expr env e0 v q xq)
  | Eraise (xs, e0) ->
      let v, q = try Mexn.find xs xq with Not_found ->
        res_of_expr e0, t_true in
      vc_label e (wp_expr env e0 v q xq)
  | _ -> assert false (* TODO *)

and sp_expr env e res mpv xmpv = assert (is_fresh res); match e.e_node with
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
      let eff = e.e_effect in
      let cq = sp_of_post expl_post res c.cty_post in
      let ne = bind_oldies c (sp_havoc env eff res cq mpv) in
      let join cq (v,mpv) =
        let cq = sp_of_post expl_xpost v cq in
        bind_oldies c (sp_havoc env eff v cq mpv) in
      let ex = merge_mexn join (cty_xpost_real c) xmpv in
      out_label e (wp_of_pre expl_pre c.cty_pre, ne, ex)
  | Elet (LDvar _, _)
  | Ecase (_, [{pp_pat = {pat_node = Pvar _}}, _]) ->
      sp_seq env e res mpv xmpv empty_out
  | Ecase (_, [pp, _]) when anon_pat pp ->
      sp_seq env e res mpv xmpv empty_out
  | Eif (e0, e1, e2) ->
      let eff = eff_union_par e1.e_effect e2.e_effect in
      let aff = mpv_affected eff mpv in
      let xaff = xmpv_affected eff xmpv in
      let out1 = sp_expr env e1 res mpv xmpv in
      let out2 = sp_expr env e2 res mpv xmpv in
      let ok1, ne1, ex1 = out_complete e1.e_effect out1 aff xaff in
      let ok2, ne2, ex2 = out_complete e2.e_effect out2 aff xaff in
      let v = res_of_expr e0 in
      let test = t_equ (t_var v) t_bool_true in
      let ok = wp_if test ok1 ok2 in
      let ne = t_if_simp test ne1 ne2 in
      let ex = merge_mexn (t_if_simp test) ex1 ex2 in
      let mpv = step_back e0.e_effect.eff_covers
                    eff.eff_reads eff.eff_covers mpv in
      out_label e (sp_seq env e0 v mpv xmpv (ok,ne,ex))
  | Ecase (e0, bl) ->
      let eff = List.fold_left (fun acc (p,e) ->
        let pvs = pvs_of_vss Spv.empty p.pp_pat.pat_vars in
        let eff = eff_bind pvs e.e_effect in
        eff_union_par acc eff) eff_empty bl in
      let aff = mpv_affected eff mpv in
      let xaff = xmpv_affected eff xmpv in
      let outl = List.map (fun ({pp_pat = p}, e) ->
        let out = sp_expr env e res mpv xmpv in
        let out = out_complete e.e_effect out aff xaff in
        out_map (t_close_branch p) out) bl in
      let v = res_of_expr e0 in
      let t = t_var v in
      let ok = wp_case t (List.map (fun (ok,_,_) -> ok) outl) in
      let ne = t_case_simp t (List.map (fun (_,ne,_) -> ne) outl) in
      let xbl = Mexn.map (fun _ -> []) xaff in
      let xbl = List.fold_right (fun (_,_,ex) xbl ->
        merge_mexn (fun x l -> x::l) ex xbl) outl xbl in
      let ex = Mexn.map (t_case_simp t) xbl in
      let mpv = step_back e0.e_effect.eff_covers
                    eff.eff_reads eff.eff_covers mpv in
      out_label e (sp_seq env e0 v mpv xmpv (ok,ne,ex))
  | Eraise (xs, e0) ->
      let v, mpv = try Mexn.find xs xmpv with Not_found ->
        res_of_expr e0, Mpv.empty in
      let ok, ne, ex = sp_expr env e0 v mpv xmpv in
      let join _ sp1 sp2 = Some (sp_or sp1 sp2) in
      let ex = Mexn.union join ex (Mexn.singleton xs ne) in
      out_label e (ok, t_false, ex)
  | _ -> assert false (* TODO *)

and sp_seq env e res mpv xmpv out = match e.e_node with
  | Elet (LDvar ({pv_vs = v}, e0), e1)
  | Ecase (e0, [{pp_pat = {pat_node = Pvar v}}, e1]) ->
      let u = new_of_vs v in (* FIXME: why push labels? *)
      let push = Slab.mem proxy_label v.vs_name.id_label in
      let e1 = if push then e_label_copy e e1 else e1 in
      let out = sp_seq env e1 res mpv xmpv out in
      let out = out_map (t_subst (Mvs.singleton v (t_var u))) out in
      let rd1 = Spv.remove (restore_pv v) e1.e_effect.eff_reads in
      let mpv = step_back e0.e_effect.eff_covers
                      rd1 e1.e_effect.eff_covers mpv in
      let sp = sp_seq env e0 u mpv xmpv out in
      if push then sp else out_label e sp
  | Ecase (e0, [pp, e1]) when anon_pat pp ->
      let out = sp_seq env e1 res mpv xmpv out in
      let mpv = step_back e0.e_effect.eff_covers
        e1.e_effect.eff_reads e1.e_effect.eff_covers mpv in
      out_label e (sp_seq env e0 (res_of_expr e0) mpv xmpv out)
  | _ ->
      let ok2, ne2, ex2 = out in
      let ok1, ne1, ex1 = sp_expr env e res mpv xmpv in
      let ok = wp_and ok1 (sp_close res mpv ne1 ok2) in
      let shift sp = sp_and ne1 (advance mpv sp) in
      let join _ sp1 sp2 = Some (sp_or sp1 sp2) in
      let ex = Mexn.union join ex1 (Mexn.map shift ex2) in
      ok, shift ne2, ex

and vc_fun env c e =
  let p = sp_of_pre expl_pre c.cty_pre in
  let args = List.map (fun v -> v.pv_vs) c.cty_args in
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
  let f = wp_forall (Mvs.keys (t_freevars Mvs.empty f)) f in
  create_pure_decl (create_prop_decl Pgoal pr f)

let vc env kn d = match d.pd_node with
  | PDlet (LDsym (s, {c_node = Cfun e; c_cty = cty})) ->
      let env = mk_env env kn in
      let f = vc_fun env cty e in
      [mk_vc_decl s.rs_name f]
  | _ -> []
