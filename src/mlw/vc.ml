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

let clone_vs v = create_vsymbol (id_clone v.vs_name) v.vs_ty
let clone_pv v = clone_vs v.pv_vs

let old_of_pv {pv_vs = v; pv_ity = ity} =
  create_pvsymbol ~ghost:true (id_clone v.vs_name) (ity_purify ity)

(* TODO? take a string as an argument? many of these are proxies *)
let res_of_ty ty = create_vsymbol (id_fresh "result") ty
let res_of_ity ity = res_of_ty (ty_of_ity ity)

let res_of_expr e =
  create_vsymbol (id_fresh ?loc:e.e_loc "result") (ty_of_ity e.e_ity)

let vc_freepvs s v q = pvs_of_vss s (Mvs.remove v (t_freevars Mvs.empty q))

let sp_label = Ident.create_label "vc:sp"
let wp_label = Ident.create_label "vc:wp"

(* VCgen environment *)

type vc_env = {
  known_map : Pdecl.known_map;
  letrec_ps : (variant list * lsymbol option list) Mls.t;
  ps_int_le : lsymbol;
  ps_int_ge : lsymbol;
  ps_int_lt : lsymbol;
  ps_int_gt : lsymbol;
  fs_int_pl : lsymbol;
  fs_int_mn : lsymbol;
}

let mk_env {Theory.th_export = ns} kn = {
  known_map = kn;
  letrec_ps = Mls.empty;
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
  let lab = Ident.Slab.remove sp_label lab in
  let lab = Ident.Slab.remove wp_label lab in
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
let expl_variant   = Ident.create_label "expl:variant decrease"

let lab_has_expl = let expl_regexp = Str.regexp "expl:" in
  Slab.exists (fun l -> Str.string_match expl_regexp l.lab_string 0)

let vc_expl lab f =
  let f = if Slab.mem stop_split f.t_label
    then f else t_label_add stop_split f in
  if lab_has_expl f.t_label then f else t_label_add lab f

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
  | Tnot c, Ttrue, _  when can_simp wp1 -> sp_implies c wp2
  | _, Ttrue, _  when can_simp wp1 -> sp_implies (t_not c) wp2
  | _, _, Ttrue  when can_simp wp2 -> sp_implies c wp1
  | _, _, _ -> t_if c wp1 wp2

let wp_case t bl =
  let check b = can_simp (snd (t_open_branch b)) in
  if List.for_all check bl then t_true else t_case t bl

let wp_forall vl wp = t_forall_close_simp vl [] wp

let wp_let v t wp = t_let_close_simp v t wp

(* exception-related tools *)

let union_mexn xsp1 xsp2 =
  Mexn.union (fun _ sp1 sp2 -> Some (sp_or sp1 sp2)) xsp1 xsp2

let inter_mexn fn xsp xwp =
  Mexn.inter (fun _ sp wp -> Some (fn sp wp)) xsp xwp

let wp_inter_mexn wp fn xsp xwp =
  Mexn.fold (fun _ g f -> wp_and f g) (inter_mexn fn xsp xwp) wp

let sp_inter_mexn sp fn xsp xsp' =
  Mexn.fold (fun _ g f -> sp_or f g) (inter_mexn fn xsp xsp') sp

let cty_xpost_real c = (* drop raises {X -> false} *)
  Mexn.set_inter c.cty_xpost c.cty_effect.eff_raises

let res_of_xbranch xs vl map out = match vl with
  | [] -> res_of_ty ty_unit, out
  | [v] -> v.pv_vs, out
  | vl ->
      let v = res_of_ity xs.xs_ity in
      let cs = fs_tuple (List.length vl) in
      let pl = List.map (fun v -> pat_var v.pv_vs) vl in
      let p = pat_app cs pl v.vs_ty and t = t_var v in
      v, map (fun f -> t_case_close t [p, f]) out

(* variant decrease pre-conditions *)

let decrease_alg env loc old_t t =
  let oty = t_type old_t and nty = t_type t in
  let quit () = Loc.errorm ?loc "no default order for %a" Pretty.print_term t in
  let ts = match oty with {ty_node = Tyapp (ts,_)} -> ts | _ -> quit () in
  let itd = find_its_defn env.known_map (restore_its ts) in
  let get_cs rs = match rs.rs_logic with RLls cs -> cs | _ -> quit () in
  let csl = List.map get_cs itd.itd_constructors in
  if csl = [] then quit ();
  let sbs = ty_match Mtv.empty (ty_app ts (List.map ty_var ts.ts_args)) oty in
  let add_arg fty acc =
    let fty = ty_inst sbs fty in
    if ty_equal fty nty then
      let vs = create_vsymbol (id_fresh "f") nty in
      pat_var vs, t_or_simp (t_equ (t_var vs) t) acc
    else pat_wild fty, acc in
  let add_cs cs =
    let pl, f = Lists.map_fold_right add_arg cs.ls_args t_false in
    t_close_branch (pat_app cs pl oty) f in
  t_case old_t (List.map add_cs csl)

let decrease_def env loc old_t t =
  if ty_equal (t_type old_t) ty_int && ty_equal (t_type t) ty_int
  then t_and (ps_app env.ps_int_le [t_nat_const 0; old_t])
             (ps_app env.ps_int_lt [t; old_t])
  else decrease_alg env loc old_t t

let decrease env loc olds news =
  let rec decr olds news = match olds, news with
    | (old_t, Some old_r)::olds, (t, Some r)::news
      when oty_equal old_t.t_ty t.t_ty && ls_equal old_r r ->
        let dt = ps_app r [t; old_t] in
        t_or_simp dt (t_and_simp (t_equ old_t t) (decr olds news))
    | (old_t, None)::olds, (t, None)::news
      when oty_equal old_t.t_ty t.t_ty ->
        let dt = decrease_def env loc old_t t in
        t_or_simp dt (t_and_simp (t_equ old_t t) (decr olds news))
    | (old_t, None)::_, (t, None)::_ ->
        decrease_def env loc old_t t
    | _ -> t_false in
  t_label ?loc Slab.empty (decr olds news)

(* convert user specifications into wp and sp *)

let t_var_or_void v =
  if ty_equal v.vs_ty ty_unit then t_void else t_var v

let wp_of_pre ({letrec_ps = lps} as env) loc lab = function
  | {t_node = Tapp (ls, tl)} :: pl when Mls.mem ls lps ->
      let olds, rels = Mls.find ls lps in
      let news = List.combine tl rels in
      let p = decrease env loc olds news in
      let p = vc_expl expl_variant p in
      t_and_l (p :: List.map (vc_expl lab) pl)
  | pl -> t_and_l (List.map (vc_expl lab) pl)

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

let sp_of_post lab v ql =
  let t = t_var_or_void v in
  (* remove the post-condition of () *)
  let push q = match open_post_with t q with
    | {t_node = Tapp (ps, [_; {t_ty = Some ty}])}
      when ls_equal ps ps_equ && ty_equal ty ty_unit -> t_true
    | f -> push_stop lab f in
  t_and_l (List.map push ql)

(* a type is affected if a modified region is reachable from it *)

let ity_affected wr ity = Util.any ity_rch_fold (Mreg.contains wr) ity

let pv_affected wr v = ity_affected wr v.pv_ity

let rec reg_aff_regs wr s reg =
  let q = reg_exp_fold (reg_aff_regs wr) Sreg.empty reg in
  let affect = not (Sreg.is_empty q) || Mreg.mem reg wr in
  Sreg.union s (if affect then Sreg.add reg q else q)

let ity_aff_regs wr s ity = ity_exp_fold (reg_aff_regs wr) s ity

(* a "destination map" maps program variables (pre-effect state)
   to fresh vsymbols (post-effect state) *)

let dst_of_pvs cv pvs = (* check that cv is non-empty at the call site *)
  let conv v () = if pv_affected cv v then Some (clone_pv v) else None in
  Mpv.mapi_filter conv pvs

let dst_of_wp cv wp =
  if Sreg.is_empty cv then Mpv.empty else
  dst_of_pvs cv (t_freepvs Spv.empty wp)

let dst_affected {eff_covers = cv} dst =
  if Mreg.is_empty cv then Mpv.empty else
  Mpv.filter (fun v _ -> pv_affected cv v) dst

let dst_step_back_raw cv1 rd2 cv2 dst =
  if Mreg.is_empty cv1 then Mpv.empty else
  let back o n =
    if not (pv_affected cv1 o) then None else
    if not (pv_affected cv2 o) then Some n else
    Some (clone_pv o) in
  Mpv.set_union (Mpv.mapi_filter back dst)
    (dst_of_pvs cv1 (Mpv.set_diff rd2 dst))

let dst_step_back eff1 eff2 dst =
  dst_step_back_raw eff1.eff_covers
    eff2.eff_reads eff2.eff_covers dst

let advancement dst = Mpv.fold (fun v n sbs ->
  Mvs.add v.pv_vs (t_var n) sbs) dst Mvs.empty

let adjustment dst dst' =
  let pair _ v n =
    if vs_equal v n then None else Some (v,n) in
  let add _ (v,n) sbs = Mvs.add v (t_var n) sbs in
  Mpv.fold add (Mpv.inter pair dst dst') Mvs.empty

(* combine postconditions with preconditions *)

let wp_close lab v ql wp =
  wp_forall [v] (sp_implies (sp_of_post lab v ql) wp)

let is_fresh v =
  try ignore (restore_pv v); false with Not_found -> true

let extract_defn v sp =
  let rec extract h = match h.t_node with
    | Tapp (ps, [{t_node = Tvar u}; t])
      when ls_equal ps ps_equ && vs_equal u v && t_v_occurs v t = 0 ->
        t, t_true
    | Tbinop (Tand,f,g) ->
        let t, f = extract f in
        t, t_label_copy h (sp_and f g)
    | _ -> raise Exit in
  try Some (extract sp) with Exit -> None

let sp_wp_close v sp adv wp =
  let wp  = t_subst adv wp in
  let fvs = t_freevars Mvs.empty sp in
  let fvs = Mvs.filter (fun v _ -> is_fresh v) fvs in
  let fvs = Mvs.fold (fun _ t s -> t_freevars s t) adv fvs in
  let vl  = List.rev (Mvs.keys (Mvs.remove v fvs)) in
  match extract_defn v sp with
  | Some (t, sp) -> wp_forall vl (wp_let v t (sp_implies sp wp))
  | None         -> wp_forall (v :: vl)      (sp_implies sp wp)

let sp_sp_close v sp adv sp' =
  let sp' = t_subst adv sp' in
  match extract_defn v sp with
  | Some (t, sp) ->                    wp_let v t (sp_and sp sp')
  | None when is_fresh v ->                        sp_and sp sp'
  | None -> t_subst_single v (t_var (clone_vs v)) (sp_and sp sp')

(* express shared region values as "v.f1.f2.f3" when possible *)

let rec explore_paths kn aff regs t ity =
  if ity.ity_imm then regs else
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg r when not (Sreg.mem r aff) -> regs
  | Ityreg ({reg_its = s; reg_args = tl; reg_regs = rl} as r) ->
      let rec height t = match t.t_node with
        (* prefer user variables to proxy variables *)
        | Tvar v when Slab.mem proxy_label v.vs_name.id_label -> 65536
        | Tvar _ -> 0 | Tapp (_,[t]) -> height t + 1
        | _ -> assert false (* shouldn't happen *) in
      let min t o = if height t < height o then t else o in
      let regs = Mreg.change (fun o -> Some (Opt.fold min t o)) r regs in
      explore_its kn aff regs t s tl rl
  | Ityapp (s,tl,rl) -> explore_its kn aff regs t s tl rl

and explore_its kn aff regs t s tl rl =
  let isb = its_match_regs s tl rl in
  let follow regs rs =
    let ity = ity_full_inst isb rs.rs_cty.cty_result in
    let ls = ls_of_rs rs and ty = Some (ty_of_ity ity) in
    explore_paths kn aff regs (t_app ls [t] ty) ity in
  List.fold_left follow regs (find_its_defn kn s).itd_fields

let name_regions kn wr dst =
  let collect o _ aff = ity_aff_regs wr aff o.pv_ity in
  let aff = Mpv.fold collect dst Sreg.empty in
  let fill o n regs = explore_paths kn aff regs (t_var n) o.pv_ity in
  let regs = Mpv.fold fill dst Mreg.empty in
  let complete r nm _ = if nm <> None then nm else
    let ty = ty_app r.reg_its.its_ts (List.map ty_of_ity r.reg_args) in
    Some (t_var (create_vsymbol (id_clone r.reg_name) ty)) in
  Mreg.merge complete regs aff

(* produce a rebuilding postcondition after a write effect *)

let cons_t_simp nt t fl =
  if t_equal nt t then fl else t_equ nt t :: fl

let rec havoc kn wr regs t ity fl =
  if not (ity_affected wr ity) then t, fl else
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg ({reg_its = s} as r) when s.its_nonfree || Mreg.mem r wr ->
      let itd = find_its_defn kn s in
      let isb = its_match_regs s r.reg_args r.reg_regs in
      let wfs = Mreg.find_def Mpv.empty r wr in
      let nt = Mreg.find r regs in
      let field rs fl =
        if Mpv.mem (Opt.get rs.rs_field) wfs then fl else
        let ity = ity_full_inst isb rs.rs_cty.cty_result in
        let ls = ls_of_rs rs and ty = Some (ty_of_ity ity) in
        let t = t_app ls [t] ty and nt = t_app ls [nt] ty in
        let t, fl = havoc kn wr regs t ity fl in
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
            let t, fl = havoc kn wr regs t ity fl in
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
              let t, fl = havoc kn wr regs (t_var v) ity fl in
              t::tl, fl in
            let tl, fl = List.fold_right2 field vl ityl ([],[]) in
            (p, fs_app cs tl ty), (p, t_and_l fl) in
          let tbl, fbl = List.split (List.map branch cl) in
          let t = t_case_close t tbl and f = t_case_close_simp t fbl in
          t, begin match f.t_node with Ttrue -> fl | _ -> f::fl end
      end

let print_dst dst = if Debug.test_flag debug then
  Format.printf "@[vars = %a@]@." (Pp.print_list Pp.space
    (fun fmt (o,n) -> Format.fprintf fmt "(%a -> %a)"
      Ity.print_pv o Pretty.print_vs n)) (Mpv.bindings dst)

let print_regs regs = if Debug.test_flag debug then
  Format.printf "@[regs = %a@]@." (Pp.print_list Pp.space
    (fun fmt (r,t) -> Format.fprintf fmt "(%a -> %a)"
      Ity.print_reg r Pretty.print_term t)) (Mreg.bindings regs)

let wp_havoc {known_map = kn} {eff_writes = wr; eff_covers = cv} wp =
  let dst = dst_of_wp cv wp in
  if Mpv.is_empty dst then wp else
  let regs = name_regions kn cv dst in
  let () = print_dst dst; print_regs regs in
  let add _ t fvs = t_freevars fvs t in
  let fvs = Mreg.fold add regs Mvs.empty in
  let update {pv_vs = o; pv_ity = ity} n wp =
    let t, fl = havoc kn wr regs (t_var o) ity [] in
    if Mvs.mem n fvs then
      sp_implies (t_and_l (cons_t_simp (t_var n) t fl)) wp
    else wp_let n t (sp_implies (t_and_l fl) wp) in
  let wp = t_subst (advancement dst) wp in
  let wp = Mpv.fold update dst wp in
  wp_forall (Mvs.keys fvs) wp

let sp_havoc {known_map = kn} {eff_writes = wr; eff_covers = cv} res sp dst =
  if Sreg.is_empty cv then sp else
  let rd = vc_freepvs Spv.empty res sp in
  let dst = dst_step_back_raw cv rd Mreg.empty dst in
  if Mpv.is_empty dst then sp else
  let regs = name_regions kn cv dst in
  let () = print_dst dst; print_regs regs in
  let update {pv_vs = o; pv_ity = ity} n sp =
    let t, fl = havoc kn wr regs (t_var o) ity [] in
    sp_and (t_and_l (cons_t_simp (t_var n) t fl)) sp in
  let sp = t_subst (advancement dst) sp in
  sp_and sp (Mpv.fold update dst t_true)

let sp_complete {eff_covers = cv} sp dst =
  let check o n sp =
    if pv_affected cv o then sp else
    sp_and sp (t_equ (t_var n) (t_var o.pv_vs)) in
  Mpv.fold check dst sp

(* fast-related tools *)

let out_map fn (ok, ne, ex) = fn ok, fn ne, Mexn.map fn ex

let out_label e out = out_map (vc_label e) out

let out_complete eff (ok, ne, ex) xres dst =
  let join _ sp xres = match sp, xres with
    | Some sp, Some _ -> Some (sp_complete eff sp dst)
    | None, Some _ -> Some t_false | _, None -> None in
  ok, sp_complete eff ne dst, Mexn.merge join ex xres

(* classical WP / fast WP *)

let anon_pat pp = Svs.is_empty pp.pp_pat.pat_vars

let bind_oldies c f =
  let sbs = Mpv.fold (fun {pv_vs = o} {pv_vs = v} s ->
    Mvs.add o (t_var v) s) c.cty_oldies Mvs.empty in
  t_subst sbs f

let rec wp_expr env e res q xq = match e.e_node with
  | _ when Slab.mem sp_label e.e_label ->
      let cv = e.e_effect.eff_covers in
      let xq = Mexn.set_inter xq e.e_effect.eff_raises in
      let dst = if Sreg.is_empty cv then Mpv.empty else
        let pvs_of_xwp _ (v,q) s = vc_freepvs s v q in
        let pvs = Mexn.fold pvs_of_xwp xq Spv.empty in
        dst_of_pvs cv (vc_freepvs pvs res q) in
      (* compute sp_expr e independently of q *)
      let ok, ne, ex = sp_expr env e res (Mexn.map fst xq) dst in
      let adv = advancement dst in
      let q = sp_wp_close res ne adv q in
      let join cq (v,q) = sp_wp_close v cq adv q in
      wp_and ok (wp_inter_mexn q join ex xq)
(*    (* compute sp_expr e with q inlined into ok, so that
         the result expression can be substituted into q *)
      let out = q, t_true, Mexn.empty in
      let ok,_,ex = sp_seq env e res (Mexn.map fst xq) out eff_empty dst in
      let adv = if Mexn.is_empty ex then Mvs.empty else advancement dst in
      wp_inter_mexn ok (fun sp (v,q) -> sp_wp_close v sp adv q) ex xq
*)
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
      let q = wp_close expl_post res c.cty_post q in
      let join cq (v,q) = wp_close expl_xpost v cq q in
      let w = wp_inter_mexn q join (cty_xpost_real c) xq in
      let w = bind_oldies c (wp_havoc env c.cty_effect w) in
      vc_label e (wp_and (wp_of_pre env e.e_loc expl_pre c.cty_pre) w)

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
  | Etry (e0, bl) ->
      let branch xs (vl,e) =
        let wp = wp_expr env e res q xq in
        res_of_xbranch xs vl (fun fn -> fn) wp in
      let xq = Mexn.set_union (Mexn.mapi branch bl) xq in
      vc_label e (wp_expr env e0 res q xq)
  | Eraise (xs, e0) ->
      let v, q = try Mexn.find xs xq with Not_found ->
        res_of_expr e0, t_true in
      vc_label e (wp_expr env e0 v q xq)
  | _ -> assert false (* TODO *)

and sp_expr env e res xres dst = match e.e_node with
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
      let sp_of_post lab v ql =
        let cq = sp_of_post lab v ql in
        let sp = sp_havoc env e.e_effect v cq dst in
        bind_oldies c sp in
      let ne = sp_of_post expl_post res c.cty_post in
      let join v ql = sp_of_post expl_xpost v ql in
      let ex = inter_mexn join xres (cty_xpost_real c) in
      out_label e (wp_of_pre env e.e_loc expl_pre c.cty_pre, ne, ex)

  | Elet (LDvar ({pv_vs = v}, e0), e1) (* FIXME: what for? *)
    when Slab.mem proxy_label v.vs_name.id_label ->
    (* we push the label down, past the inserted "let" *)
      let e1 = e_label_copy e e1 in
      let out = sp_expr env e1 res xres dst in
      sp_pred_let env e0 v xres out e1 eff_empty dst
  | Elet (LDvar ({pv_vs = v}, e0), e1)
  | Ecase (e0, [{pp_pat = {pat_node = Pvar v}}, e1]) ->
      let out = sp_expr env e1 res xres dst in
      out_label e (sp_pred_let env e0 v xres out e1 eff_empty dst)
  | Ecase (e0, [pp, e1]) when anon_pat pp ->
      let v = res_of_expr e0 in
      let out = sp_expr env e1 res xres dst in
      out_label e (sp_pred_seq env e0 v xres out e1 eff_empty dst)


  | Eif (e0, e1, e2) ->
      let eff = eff_union_par e1.e_effect e2.e_effect in
      let xres' = Mexn.set_inter xres eff.eff_raises in
      let dst' = dst_affected eff dst in
      let out1 = sp_expr env e1 res xres' dst' in
      let out2 = sp_expr env e2 res xres' dst' in
      let ok1, ne1, ex1 = out_complete e1.e_effect out1 xres' dst' in
      let ok2, ne2, ex2 = out_complete e2.e_effect out2 xres' dst' in
      let v = res_of_expr e0 in
      let test = t_equ (t_var v) t_bool_true in
      let ok = wp_if test ok1 ok2 in
      let ne = t_if_simp test ne1 ne2 in
      let ex = inter_mexn (t_if_simp test) ex1 ex2 in
      out_label e (sp_seq env e0 v xres (ok,ne,ex) eff dst)
  | Ecase (e0, bl) ->
      let eff = List.fold_left (fun acc (p,e) ->
        let pvs = pvs_of_vss Spv.empty p.pp_pat.pat_vars in
        let eff = eff_bind pvs e.e_effect in
        eff_union_par acc eff) eff_empty bl in
      let xres' = Mexn.set_inter xres eff.eff_raises in
      let dst' = dst_affected eff dst in
      let outl = List.map (fun ({pp_pat = p}, e) ->
        let out = sp_expr env e res xres' dst' in
        let out = out_complete e.e_effect out xres' dst' in
        out_map (t_close_branch p) out) bl in
      let v = res_of_expr e0 in
      let t = t_var v in
      let ok = wp_case t (List.map (fun (ok,_,_) -> ok) outl) in
      let ne = t_case_simp t (List.map (fun (_,ne,_) -> ne) outl) in
      let xbl = Mexn.map (fun _ -> []) xres' in
      let xbl = List.fold_right (fun (_,_,ex) xbl ->
        inter_mexn (fun x l -> x::l) ex xbl) outl xbl in
      let ex = Mexn.map (t_case_simp t) xbl in
      out_label e (sp_seq env e0 v xres (ok,ne,ex) eff dst)
  | Etry (e0, xl) ->
      let eff = Mexn.fold (fun _ (vl,e) acc ->
        let eff = eff_bind (Spv.of_list vl) e.e_effect in
        eff_union_par acc eff) xl eff_empty in
      let xres' = Mexn.set_inter xres eff.eff_raises in
      let dst' = dst_affected eff dst in
      let branch xs (vl,e) =
        let out = sp_expr env e res xres' dst' in
        let out = out_complete e.e_effect out xres' dst' in
        res_of_xbranch xs vl out_map out in
      let outm = Mexn.mapi branch xl in
      let xres = Mexn.set_union (Mexn.map fst outm) xres in
      let dst = dst_step_back e0.e_effect eff dst in
      let ok, ne, ex = sp_expr env e0 res xres dst in
      let adv = if Mexn.is_empty outm then Mvs.empty else advancement dst in
      let join sp (v,(ok,_,_)) = sp_wp_close v sp adv ok in
      let ok = wp_inter_mexn ok join ex outm in
      let adj = adjustment dst dst' in
      let adjust sp = sp_complete e0.e_effect (t_subst adj sp) dst' in
      let join sp (v,(_,ne,_)) = sp_sp_close v sp adv ne in
      let ne = sp_inter_mexn (adjust ne) join ex outm in
      let join sp (v,(_,_,ex)) = Mexn.map (sp_sp_close v sp adv) ex in
      let ex = Mexn.fold (fun _ x1 x2 -> union_mexn x2 x1)
        (inter_mexn join ex outm)
        (Mexn.map adjust (Mexn.set_diff ex outm)) in
      out_label e (ok, ne, ex)
  | Eraise (xs, e0) ->
      let v = try Mexn.find xs xres with Not_found -> res_of_expr e0 in
      let ok, ne, ex = sp_expr env e0 v xres dst in
      let ex = union_mexn ex (Mexn.singleton xs ne) in
      out_label e (ok, t_false, ex)
  | _ -> assert false (* TODO *)

and sp_pred_let env e0 res xres out e1 eff dst =
  let eff1 = eff_bind_single (restore_pv res) e1.e_effect in
  let eff = eff_union_seq eff1 eff in
  sp_seq env e0 res xres out eff dst

and sp_pred_seq env e0 res xres out e1 eff dst =
  let eff = eff_union_seq e1.e_effect eff in
  sp_seq env e0 res xres out eff dst

and sp_seq env e res xres out eff dst = match e.e_node with
  | Elet (LDvar ({pv_vs = v}, e0), e1) (* FIXME: what for? *)
    when Slab.mem proxy_label v.vs_name.id_label ->
    (* we push the label down, past the inserted "let" *)
      let e1 = e_label_copy e e1 in
      let out = sp_seq env e1 res xres out eff dst in
      sp_pred_let env e0 v xres out e1 eff dst
  | Elet (LDvar ({pv_vs = v}, e0), e1)
  | Ecase (e0, [{pp_pat = {pat_node = Pvar v}}, e1]) ->
      let out = sp_seq env e1 res xres out eff dst in
      out_label e (sp_pred_let env e0 v xres out e1 eff dst)
  | Ecase (e0, [pp, e1]) when anon_pat pp ->
      let v = res_of_expr e0 in
      let out = sp_seq env e1 res xres out eff dst in
      out_label e (sp_pred_seq env e0 v xres out e1 eff dst)
  | Eghost e1 ->
      sp_seq env (e_label_copy e e1) res xres out eff dst
  | _ ->
      let ok2, ne2, ex2 = out in
      let dst' = dst_affected eff dst in
      let dst = dst_step_back e.e_effect eff dst in
      let ok1, ne1, ex1 = sp_expr env e res xres dst in
      let adv = advancement dst in
      let ok = wp_and ok1 (sp_wp_close res ne1 adv ok2) in
      let shift sp = sp_sp_close res ne1 adv sp in
      let adj =
        if Mexn.is_empty ex1 then Mvs.empty else adjustment dst dst' in
      let adjust sp = sp_complete e.e_effect (t_subst adj sp) dst' in
      let ex = union_mexn (Mexn.map adjust ex1) (Mexn.map shift ex2) in
      ok, shift ne2, ex

and vc_fun env ?(olds=Mvs.empty) c e =
  let p = sp_of_pre expl_pre c.cty_pre in
  let args = List.map (fun v -> v.pv_vs) c.cty_args in
  let mk_xq xs xq = wp_of_post expl_xpost xs.xs_ity xq in
  let r,q = wp_of_post expl_post c.cty_result c.cty_post in
  let w = wp_expr env e r q (Mexn.mapi mk_xq c.cty_xpost) in
  wp_forall args (sp_implies p (t_subst olds (bind_oldies c w)))

and vc_rec ({letrec_ps = lps} as env) rdl =
  let vc_rd {rec_fun = c; rec_varl = varl} =
    let e = match c.c_node with Cfun e -> e | _ -> assert false in
    if varl = [] then vc_fun env c.c_cty e else
    let fpv = Mpv.mapi_filter (fun v _ -> (* oldify mutable vars *)
      if ity_immutable v.pv_ity then None else Some (old_of_pv v))
      (List.fold_left (fun s (t,_) -> t_freepvs s t) Spv.empty varl) in
    let olds = Mpv.fold (fun v o s ->
      Mvs.add o.pv_vs (t_var v.pv_vs) s) fpv Mvs.empty in
    let news = Mpv.fold (fun v o s ->
      Mvs.add v.pv_vs (t_var o.pv_vs) s) fpv Mvs.empty in
    let varl = if Mvs.is_empty news then varl else
      List.map (fun (t,r) -> t_subst news t, r) varl in
    let add lps rd = let decr = ls_decr_of_rec_defn rd in
      Mls.add (Opt.get decr) (varl, List.map snd rd.rec_varl) lps in
    let env = { env with letrec_ps = List.fold_left add lps rdl } in
    vc_fun env ~olds c.c_cty e in
  List.map vc_rd rdl

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
  | PDlet (LDrec rdl) ->
      let env = mk_env env kn in
      let fl = vc_rec env rdl in
      List.map2 (fun rd f -> mk_vc_decl rd.rec_sym.rs_name f) rdl fl
  | _ -> []
