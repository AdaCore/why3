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

let debug = Debug.register_info_flag "vc_debug"
  ~desc:"Print@ details@ of@ verification@ conditions@ generation."

let debug_sp = Debug.register_flag "vc_sp"
  ~desc:"Use@ 'Efficient@ Weakest@ Preconditions'@ for@ verification."

let no_eval = Debug.register_flag "vc_no_eval"
  ~desc:"Do@ not@ simplify@ pattern@ matching@ on@ record@ datatypes@ in@ VCs."

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
  if e.e_loc = None && Slab.is_empty e.e_label then f else
  let loc = if f.t_loc = None then e.e_loc else f.t_loc in
  let lab = Ident.Slab.union e.e_label f.t_label in
  let lab = Ident.Slab.remove sp_label lab in
  let lab = Ident.Slab.remove wp_label lab in
  t_label ?loc lab f

let expl_pre       = Ident.create_label "expl:precondition"
let expl_post      = Ident.create_label "expl:postcondition"
let expl_xpost     = Ident.create_label "expl:exceptional postcondition"
let expl_assume    = Ident.create_label "expl:assumption"
let expl_assert    = Ident.create_label "expl:assertion"
let expl_check     = Ident.create_label "expl:check"
let expl_absurd    = Ident.create_label "expl:unreachable point"
let expl_loop_init = Ident.create_label "expl:loop invariant init"
let expl_loop_keep = Ident.create_label "expl:loop invariant preservation"
let expl_loop_vari = Ident.create_label "expl:loop variant decrease"
let expl_variant   = Ident.create_label "expl:variant decrease"
let _expl_type_inv  = Ident.create_label "expl:type invariant"

let lab_has_expl = let expl_regexp = Str.regexp "expl:" in
  Slab.exists (fun l -> Str.string_match expl_regexp l.lab_string 0)

let vc_expl loc l ({t_label = lab} as f) =
  let lab = if lab_has_expl lab then lab else Slab.add l lab in
  let loc = if loc = None then f.t_loc else loc in
  t_label ?loc (Slab.add stop_split lab) f

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

let wp_and_asym wp1 wp2 = match wp1.t_node, wp2.t_node with
  | (Ttrue, _ | _, Tfalse) when can_simp wp1 -> wp2
  | (_, Ttrue | Tfalse, _) when can_simp wp2 -> wp1
  | _, _ -> t_and_asym wp1 wp2

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

let decrease env loc lab olds news =
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
  vc_expl loc lab (decr olds news)

let oldify_variant varl =
  if varl = [] then Mvs.empty, varl else
  let fpv = Mpv.mapi_filter (fun v _ -> (* oldify mutable vars *)
    if ity_immutable v.pv_ity then None else Some (old_of_pv v))
    (List.fold_left (fun s (t,_) -> t_freepvs s t) Spv.empty varl) in
  if Mpv.is_empty fpv then Mvs.empty, varl else
  let o2n = Mpv.fold (fun v o s ->
    Mvs.add o.pv_vs (t_var v.pv_vs) s) fpv Mvs.empty in
  let n2o = Mpv.fold (fun v o s ->
    Mvs.add v.pv_vs (t_var o.pv_vs) s) fpv Mvs.empty in
  o2n, List.map (fun (t,r) -> t_subst n2o t, r) varl

(* convert user specifications into wp and sp *)

let t_var_or_void v =
  if ty_equal v.vs_ty ty_unit then t_void else t_var v

let wp_of_inv loc lab pl = t_and_l (List.map (vc_expl loc lab) pl)

let wp_of_pre ({letrec_ps = lps} as env) loc lab = function
  | {t_node = Tapp (ls, tl)} :: pl when Mls.mem ls lps ->
      let olds, rels = Mls.find ls lps in
      let news = List.combine tl rels in
      let p = decrease env loc expl_variant olds news in
      wp_and p (wp_of_inv loc lab pl)
  | pl -> wp_of_inv loc lab pl

let wp_of_post lab ity = function
  | q::ql ->
      let v, q = open_post q in let t = t_var_or_void v in
      let mk_post q = vc_expl None lab (open_post_with t q) in
      v, t_and_l (vc_expl None lab q :: List.map mk_post ql)
  | [] ->
      res_of_ity ity, t_true

let rec push_stop loc lab f = match f.t_node with
  | Tbinop (Tand,g,h) when not (Slab.mem stop_split f.t_label) ->
      t_label_copy f (t_and (push_stop loc lab g) (push_stop loc lab h))
  | _ -> vc_expl loc lab f

let sp_of_pre lab pl = t_and_l (List.map (push_stop None lab) pl)

let sp_of_post loc lab v ql =
  let t = t_var_or_void v in
  (* remove the post-condition of () *)
  let push q = match open_post_with t q with
    | {t_node = Tapp (ps, [_; {t_ty = Some ty}])}
      when ls_equal ps ps_equ && ty_equal ty ty_unit -> t_true
    | f -> push_stop loc lab f in
  t_and_l (List.map push ql)

(* a type is affected if a modified region is reachable from it *)

let ity_affected wr ity = Util.any ity_rch_fold (Mreg.contains wr) ity

let pv_affected wr v = ity_affected wr v.pv_ity

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

let wp_close loc lab v ql wp =
  let sp = sp_of_post loc lab v ql in
  match term_of_post ~prop:false v sp with
  | Some (t, sp) -> wp_let v t (sp_implies sp wp)
  | None ->      wp_forall [v] (sp_implies sp wp)

let is_fresh v =
  try ignore (restore_pv v); false with Not_found -> true

let sp_wp_close v sp adv wp =
  let wp  = t_subst adv wp in
  let fvs = t_freevars Mvs.empty sp in
  let fvs = Mvs.filter (fun v _ -> is_fresh v) fvs in
  let fvs = Mvs.fold (fun _ t s -> t_freevars s t) adv fvs in
  let vl  = List.rev (Mvs.keys (Mvs.remove v fvs)) in
  match term_of_post ~prop:false v sp with
  | Some (t, sp) -> wp_forall vl (wp_let v t (sp_implies sp wp))
  | None         -> wp_forall (v :: vl)      (sp_implies sp wp)

let sp_sp_close v sp adv sp' =
  let sp' = t_subst adv sp' in
  match term_of_post ~prop:false v sp with
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
  (* for every write collect the regions affected by it or
    reachable from it (needed for multi-staged assignment) *)
  let rec regs_to_name s r =
    let q = if Mreg.mem r wr
      then reg_rch_fold Sreg.add_left Sreg.empty r
      else reg_exp_fold regs_to_name  Sreg.empty r in
    if Sreg.is_empty q then s else Sreg.union s (Sreg.add r q) in
  let collect o _ aff = ity_exp_fold regs_to_name aff o.pv_ity in
  let aff = Mpv.fold collect dst Sreg.empty in
  let fill o n regs = explore_paths kn aff regs (t_var n) o.pv_ity in
  let regs = Mpv.fold fill dst Mreg.empty in
  let complete r nm _ = if nm <> None then nm else
    let ty = ty_app r.reg_its.its_ts (List.map ty_of_ity r.reg_args) in
    Some (t_var (create_vsymbol (id_clone r.reg_name) ty)) in
  Mreg.merge complete regs aff

(* multi-staged assignment changes the names of regions *)

let writes_of_assign asl =
  let add wr (r,f,v) =
    let f = Opt.get f.rs_field in
    let r = match r.pv_ity.ity_node with
      | Ityreg r -> r | _ -> assert false in
    Mreg.change (function
      | None   -> Some (Mpv.singleton f v)
      | Some s -> Some (Mpv.add f v s)) r wr in
  List.fold_left add Mreg.empty asl

let rename_regions regs cv wr =
  (* we compute the same region bijection as eff_assign,
     except we do not need any consistency checking now *)
  let reg_rexp {reg_its = s; reg_args = tl; reg_regs = rl} wfs =
    let ity_rexp xl t = ity_exp_fold (fun l r -> r :: l) xl t in
    let sbs = its_match_regs s tl rl in
    let mfield xl f = match Mpv.find_opt f wfs with
      | Some v -> ity_rexp xl v.pv_ity
      | None -> ity_rexp xl (ity_full_inst sbs f.pv_ity) in
    List.fold_left mfield [] s.its_mfields in
  let rec stitch t2f rf rt wfs =
    let t2f = Mreg.add rt rf t2f in
    let link t2f rf rt = stitch t2f rf rt (Mreg.find_def Mpv.empty rt wr) in
    List.fold_left2 link t2f (reg_rexp rf Mpv.empty) (reg_rexp rt wfs) in
  let add_write r wfs t2f = (* reset regions do not partake in renaming *)
    if not (Sreg.mem r cv) then t2f else stitch t2f r r wfs in
  let t2f = Mreg.fold add_write wr Mreg.empty in
  Mreg.map (fun rf -> Mreg.find rf regs) t2f

(* produce a rebuilding postcondition after a write effect *)

let cons_t_simp nt t fl =
  if t_equal nt t then fl else t_equ nt t :: fl

type rhs_of_write = PV of pvsymbol | VD | NF

let rhs_of_effect f wfs = if Mpv.mem f wfs then VD else NF

let rhs_of_assign f wfs = try PV (Mpv.find f wfs) with Not_found -> NF

let sensitive itd {pv_vs = f} =
  List.exists (fun i -> t_v_occurs f i > 0) itd.itd_invariant

let rec havoc kn get_rhs wr regs t ity fl =
  if not (ity_affected wr ity) then t, fl else
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg ({reg_its = s} as r) when s.its_nonfree || Mreg.mem r wr ->
      let itd = find_its_defn kn s in
      let isb = its_match_regs s r.reg_args r.reg_regs in
      let wfs = Mreg.find_def Mpv.empty r wr in
      let nt = Mreg.find r regs in
      let field rs fl =
        let fd = Opt.get rs.rs_field in
        match get_rhs fd wfs with
        | VD -> fl
        | PV {pv_vs = v; pv_ity = ity} ->
            if sensitive itd fd then
              assert false; (* TODO: strong invariants *)
            let nt = fs_app (ls_of_rs rs) [nt] v.vs_ty in
            let t, fl = havoc kn get_rhs wr regs (t_var v) ity fl in
            cons_t_simp nt t fl
        | NF ->
            let ity = ity_full_inst isb rs.rs_cty.cty_result in
            if ity_affected wr ity && sensitive itd fd then
              assert false; (* TODO: strong invariants *)
            let ls = ls_of_rs rs and ty = Some (ty_of_ity ity) in
            let t = t_app ls [t] ty and nt = t_app ls [nt] ty in
            let t, fl = havoc kn get_rhs wr regs t ity fl in
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
            let t, fl = havoc kn get_rhs wr regs t ity fl in
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
              let t, fl = havoc kn get_rhs wr regs (t_var v) ity fl in
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

let wp_havoc_raw kn get_rhs wr wp dst regs =
  let () = print_dst dst; print_regs regs in
  let add _ t fvs = t_freevars fvs t in
  let fvs = Mreg.fold add regs Mvs.empty in
  let update {pv_vs = o; pv_ity = ity} n wp =
    let t, fl = havoc kn get_rhs wr regs (t_var o) ity [] in
    if Mvs.mem n fvs then
      sp_implies (t_and_l (cons_t_simp (t_var n) t fl)) wp
    else wp_let n t (sp_implies (t_and_l fl) wp) in
  let wp = t_subst (advancement dst) wp in
  let wp = Mpv.fold update dst wp in
  wp_forall (Mvs.keys fvs) wp

let wp_havoc {known_map = kn} {eff_writes = wr; eff_covers = cv} wp =
  let dst = dst_of_wp cv wp in
  if Mpv.is_empty dst then wp else
  let regs = name_regions kn cv dst in
  wp_havoc_raw kn rhs_of_effect wr wp dst regs

let sp_havoc_raw kn get_rhs wr sp dst regs =
  let () = print_dst dst; print_regs regs in
  let update {pv_vs = o; pv_ity = ity} n sp =
    let t, fl = havoc kn get_rhs wr regs (t_var o) ity [] in
    sp_and (t_and_l (cons_t_simp (t_var n) t fl)) sp in
  let sp = t_subst (advancement dst) sp in
  sp_and sp (Mpv.fold update dst t_true)

let sp_havoc {known_map = kn} {eff_writes = wr; eff_covers = cv} res sp dst =
  if Sreg.is_empty cv then sp else
  let rd = vc_freepvs Spv.empty res sp in
  let dst = dst_step_back_raw cv rd Mreg.empty dst in
  if Mpv.is_empty dst then sp else
  let regs = name_regions kn cv dst in
  sp_havoc_raw kn rhs_of_effect wr sp dst regs

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

let sp_adjust eff dst dst' =
  let adj = adjustment dst dst' in
  fun sp -> sp_complete eff (t_subst adj sp) dst'

(* classical WP / fast WP *)

let anon_pat pp = Svs.is_empty pp.pp_pat.pat_vars

let bind_oldies c f =
  let sbs = Mpv.fold (fun {pv_vs = o} {pv_vs = v} s ->
    Mvs.add o (t_var v) s) c.cty_oldies Mvs.empty in
  t_subst sbs f

let spec_while env e invl varl =
  let init = wp_of_inv None expl_loop_init invl in
  let keep = wp_of_inv None expl_loop_keep invl in
  if varl = [] then init, Mvs.empty, keep else
  let o2n, olds = oldify_variant varl in
  let d = decrease env e.e_loc expl_loop_vari olds varl in
  init, o2n, wp_and keep d

let spec_for env _e v ({pv_vs = a}, d, {pv_vs = b}) invl =
  let a = t_var a and b = t_var b in
  let i = t_var v and one = t_nat_const 1 in
  let prev = wp_of_inv None expl_loop_init invl in
  let keep = wp_of_inv None expl_loop_keep invl in
  let gt, le, pl = match d with
    | To     -> env.ps_int_gt, env.ps_int_le, env.fs_int_pl
    | DownTo -> env.ps_int_lt, env.ps_int_ge, env.fs_int_mn in
  let a_gt_b = ps_app gt [a;b] and a_le_b = ps_app le [a;b] in
  let bounds = t_and (ps_app le [a;i]) (ps_app le [i;b]) in
  let init = sp_implies a_le_b (t_subst_single v a prev) in
  let keep = t_subst_single v (fs_app pl [i;one] ty_int) keep in
  let last = t_subst_single v (fs_app pl [b;one] ty_int) prev in
  a_gt_b, init, sp_and bounds prev, keep, sp_and a_le_b last

let rec wp_expr env e res q xq = match e.e_node with
  | _ when Slab.mem sp_label e.e_label ->
      let cv = e.e_effect.eff_covers in
      let xq = Mexn.set_inter xq e.e_effect.eff_raises in
      let dst = if Sreg.is_empty cv then Mpv.empty else
        let pvs_of_xwp _ (v,q) s = vc_freepvs s v q in
        let pvs = Mexn.fold pvs_of_xwp xq Spv.empty in
        dst_of_pvs cv (vc_freepvs pvs res q) in
(*
      (* compute sp_expr e independently of q *)
      let ok, ne, ex = sp_expr env e res (Mexn.map fst xq) dst in
      let adv = advancement dst in
      let q = sp_wp_close res ne adv q in
      let join cq (v,q) = sp_wp_close v cq adv q in
      wp_and ok (wp_inter_mexn q join ex xq)
*)
      (* compute sp_expr e with q inlined into ok, so that
         the result expression can be substituted into q *)
      let out = q, t_true, Mexn.empty in
      let ok,_,ex = sp_seq env e res (Mexn.map fst xq) out eff_empty dst in
      let adv = if Mexn.is_empty ex then Mvs.empty else advancement dst in
      wp_inter_mexn ok (fun sp (v,q) -> sp_wp_close v sp adv q) ex xq
  | Evar v ->
      t_subst_single res (vc_label e (t_var v.pv_vs)) q
  | Econst c ->
      t_subst_single res (vc_label e (t_const c)) q

  | Eexec (ce, c) ->
      let p = wp_of_pre env e.e_loc expl_pre c.cty_pre in
      let q = wp_close e.e_loc expl_post res c.cty_post q in
      let join cq (v,q) = wp_close e.e_loc expl_xpost v cq q in
      let w = wp_inter_mexn q join (cty_xpost_real c) xq in
      let w = bind_oldies c (wp_havoc env c.cty_effect w) in
      vc_label e (wp_and (vc_cexp env true ce) (wp_and p w))

  | Elet (LDvar ({pv_vs = v}, e0), e1)
  | Ecase (e0, [{pp_pat = {pat_node = Pvar v}}, e1]) ->
      let q = wp_expr env e1 res q xq in
      vc_label e (wp_expr env e0 v q xq)
  | Ecase (e0, [pp, e1]) when anon_pat pp ->
      let q = wp_expr env e1 res q xq in
      vc_label e (wp_expr env e0 (res_of_expr e0) q xq)

  | Elet ((LDsym _| LDrec _) as ld, e1) ->
      let q = wp_expr env e1 res q xq in
      let close_wp, _ = vc_let_sym env true ld e1 in
      vc_label e (close_wp q)
  | Eif (e0, e1, e2) when eff_pure e1.e_effect && eff_pure e2.e_effect ->
      let v, ok, ne = sp_pure_if env e0.e_loc e1 e2 res in
      let q = sp_wp_close res ne Mvs.empty q in
      vc_label e (wp_expr env e0 v (wp_and ok q) xq)
  | Eif (e0, e1, e2) ->
      let v = res_of_expr e0 in
      let test = t_equ (t_var v) t_bool_true in
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
  | Eassert (Assert, f) ->
      let q = t_subst_single res t_void q in
      wp_and_asym (vc_label e (vc_expl None expl_assert f)) q
  | Eassert (Assume, f) ->
      let q = t_subst_single res t_void q in
      sp_implies (vc_label e (vc_expl None expl_assume f)) q
  | Eassert (Check, f) ->
      let q = t_subst_single res t_void q in
      wp_and (vc_label e (vc_expl None expl_check f)) q
  | Eghost e0 ->
      vc_label e (wp_expr env e0 res q xq)
  | Epure t ->
      let t = vc_label e t in
      begin match t.t_ty with
        | Some ty when ty_equal ty ty_unit -> t_subst_single res t_void q
        | Some _ -> wp_let res t q
        | None -> wp_let res (t_if_simp t t_bool_true t_bool_false) q
      end
  | Eabsurd ->
      vc_label e (vc_expl e.e_loc expl_absurd t_false)
  | Eassign asl ->
      let q = t_subst_single res t_void q in
      let cv = e.e_effect.eff_covers in
      let dst = dst_of_wp cv q in
      if Mpv.is_empty dst then vc_label e q else
      let wr = writes_of_assign asl and kn = env.known_map in
      let regs = rename_regions (name_regions kn cv dst) cv wr in
      vc_label e (wp_havoc_raw kn rhs_of_assign wr q dst regs)
  | Ewhile (e0, invl, varl, e1) ->
      (* wp(while e0 inv I var V do e1 done, Q, R) =
         I and forall S. I ->
                 wp(e0, (if result then wp(e1, I /\ decr(V), R) else Q), R) *)
      let v = res_of_expr e0 in
      let q = t_subst_single res t_void q in
      let init, o2n, keep = spec_while env e invl varl in
      let w = wp_expr env e1 res keep xq in
      let w = wp_if (t_equ (t_var v) t_bool_true) w q in
      let w = sp_implies init (wp_expr env e0 v w xq) in
      let w = wp_havoc env e.e_effect (t_subst o2n w) in
      vc_label e (wp_and init w)
  | Efor ({pv_vs = v}, bounds, invl, e1) ->
      (* wp(for v = a to b inv I(v) do e1 done, Q, R) =
             a > b  -> Q
         and a <= b -> I(a)
         and forall S. forall v. a <= v <= b /\ I(v) -> wp(e1, I(v+1), R)
                   and a <= b /\ I(b+1) -> Q *)
      let q = t_subst_single res t_void q in
      let a_gt_b, init, prev, keep, last = spec_for env e v bounds invl in
      let w = wp_forall [v] (sp_implies prev (wp_expr env e1 res keep xq)) in
      let w = wp_havoc env e.e_effect (wp_and w (sp_implies last q)) in
      vc_label e (wp_and (sp_implies a_gt_b q) (wp_and init w))

and sp_expr env e res xres dst = match e.e_node with
  | Evar v ->
      let t = vc_label e (t_var v.pv_vs) in
      t_true, t_equ (t_var res) t, Mexn.empty
  | Econst c ->
      let t = vc_label e (t_const c) in
      t_true, t_equ (t_var res) t, Mexn.empty

  | Eexec (ce, c) ->
      let sp_of_post lab v ql =
        let cq = sp_of_post e.e_loc lab v ql in
        let sp = sp_havoc env e.e_effect v cq dst in
        bind_oldies c sp in
      let ne = sp_of_post expl_post res c.cty_post in
      let join v ql = sp_of_post expl_xpost v ql in
      let ex = inter_mexn join xres (cty_xpost_real c) in
      let ok = wp_of_pre env e.e_loc expl_pre c.cty_pre in
      out_label e (wp_and (vc_cexp env false ce) ok, ne, ex)

  | Elet (LDvar ({pv_vs = v}, e0), e1)
  | Ecase (e0, [{pp_pat = {pat_node = Pvar v}}, e1]) ->
      let out = sp_expr env e1 res xres dst in
      out_label e (sp_pred_let env e0 v xres out e1 eff_empty dst)
  | Ecase (e0, [pp, e1]) when anon_pat pp ->
      let v = res_of_expr e0 in
      let out = sp_expr env e1 res xres dst in
      out_label e (sp_pred_seq env e0 v xres out e1 eff_empty dst)

  | Elet ((LDsym _| LDrec _) as ld, e1) ->
      let ok, ne, ex = sp_expr env e1 res xres dst in
      let close_wp, close_sp = vc_let_sym env false ld e1 in
      out_label e (close_wp ok, close_sp ne, Mexn.map close_sp ex)
  | Eif (e0, e1, e2) when eff_pure e1.e_effect && eff_pure e2.e_effect ->
      let v, ok, ne = sp_pure_if env e0.e_loc e1 e2 res in
      let eff = eff_union_par e1.e_effect e2.e_effect in
      out_label e (sp_seq env e0 v xres (ok,ne,Mexn.empty) eff dst)
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
      let outm = Mexn.mapi (fun xs (vl,e) ->
        let out = sp_expr env e res xres' dst' in
        let out = out_complete e.e_effect out xres' dst' in
        res_of_xbranch xs vl out_map out) xl in
      let xres = Mexn.set_union (Mexn.map fst outm) xres in
      let dst = dst_step_back e0.e_effect eff dst in
      let ok, ne, ex = sp_expr env e0 res xres dst in
      let adv = advancement dst in
      let join sp (v,(ok,_,_)) = sp_wp_close v sp adv ok in
      let ok = wp_inter_mexn ok join ex outm in
      let adjust = sp_adjust e0.e_effect dst dst' in
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
  | Eassert (Assert, f) ->
      let ok = vc_label e (vc_expl None expl_assert f) in
      ok, ok, Mexn.empty
  | Eassert (Assume, f) ->
      t_true, vc_label e (vc_expl None expl_assume f), Mexn.empty
  | Eassert (Check, f) ->
      vc_label e (vc_expl None expl_check f), t_true, Mexn.empty
  | Eghost e0 ->
      out_label e (sp_expr env e0 res xres dst)
  | Epure t ->
      let t = vc_label e t in
      let ne = match t.t_ty with
        | Some ty when ty_equal ty ty_unit -> t_true
        | Some _ -> t_equ (t_var res) t
        | None -> t_equ (t_var res) (t_if_simp t t_bool_true t_bool_false) in
      t_true, ne, Mexn.empty
  | Eabsurd ->
      let ok = vc_label e (vc_expl e.e_loc expl_absurd t_false) in
      ok, ok, Mexn.empty
  | Eassign asl ->
      let cv = e.e_effect.eff_covers in
      let dst = dst_affected e.e_effect dst in
      if Mpv.is_empty dst then t_true, t_true, Mexn.empty else
      let wr = writes_of_assign asl and kn = env.known_map in
      let regs = rename_regions (name_regions kn cv dst) cv wr in
      let sp = sp_havoc_raw kn rhs_of_assign wr t_true dst regs in
      t_true, vc_label e sp, Mexn.empty
  | Ewhile (e0, invl, varl, e1) ->
      (* ok: I /\ !! I -> (ok0 /\ (ne0 ->  test -> ok1 /\ (ne1 -> I /\ V)))
         ne:      !! I /\         (ne0 /\ !test)
         ex:      !! I /\ (ex0 \/ (ne0 /\  test /\ ex1)) *)
      let v = res_of_expr e0 in
      let test = t_equ (t_var v) t_bool_true in
      let init, o2n, keep = spec_while env e invl varl in
      let out = keep, t_false, Mexn.empty in
      let dst = dst_affected e.e_effect dst in
      let eff = eff_read (t_freepvs Spv.empty keep) in
      let dst1 = dst_step_back e1.e_effect eff dst in
      let ne = sp_complete eff_empty (t_not test) dst1 in
      let ok, _, ex = sp_seq env e1 res xres out eff dst in
      let out = sp_implies test ok, ne, Mexn.map (sp_and test) ex in
      let ok, ne, ex = sp_pred_seq env e0 v xres out e1 eff dst in
      let src = dst_step_back e.e_effect e.e_effect dst in
      let hav = sp_havoc env e.e_effect res init src in
      let adv = advancement src in
      let ne = sp_sp_close res hav adv ne in
      let ex = Mexn.map (sp_sp_close res hav adv) ex in
      let ok = sp_wp_close res hav adv (t_subst o2n ok) in
      (* right now, ne looks like this:
           [S] havoc [S1] I /\ ne0 [S2] !test /\ dst S = S2.
         The last part was introduced by sp_complete to make
         postcondition !test consistent with the effect of e1.
         To remove the noise, every equality (x = x') in ne,
         where x in Rn dst, and x' is fresh and not in Rn dst,
         is removed and converted into substitution [x' -> x]. *)
      let finals = Mpv.fold (Util.const Svs.add) dst Svs.empty in
      let locals = Mvs.set_diff (t_freevars Mvs.empty ne) finals in
      let locals = Mvs.filter (fun v _ -> is_fresh v) locals in
      let rec clean sbs h = match h.t_node with
        | _ when Slab.mem stop_split h.t_label -> sbs, h
        | Tapp (ps, [{t_node = Tvar u} as t; {t_node = Tvar v}])
          when ls_equal ps ps_equ && Svs.mem u finals &&
               Mvs.mem v locals && not (Mvs.mem v sbs) ->
            Mvs.add v t sbs, t_true
        | Tbinop (Tand, f, g) ->
            let sbs, p = clean sbs f in let sbs, q = clean sbs g in
            sbs, if p == f && q == g then h else t_label_copy h (sp_and p q)
        | Tlet (t, bf) ->
            let v, f = t_open_bound bf in let sbs, p = clean sbs f in
            sbs, if p == f then h else t_label_copy h (wp_let v t p)
        | _ -> sbs, h in
      let sbs, ne = clean Mvs.empty ne in
      out_label e (wp_and init ok, t_subst sbs ne, ex)
  | Efor ({pv_vs = v}, bounds, invl, e1) ->
      (* ok:    a <= b -> I(a)
            and forall v. !! a <= v <= b /\ I(v) -> ok1 /\ (ne1 -> I(v+1))
         ne:                    (a > b /\ S' = S) \/ (!! a <= b /\ I(b+1))
         ex:   [exists v] !! a <= v <= b /\ I(v) /\ ex1 *)
      let a_gt_b, init, prev, keep, last = spec_for env e v bounds invl in
      let out = keep, t_false, Mexn.empty in
      let dst = dst_affected e.e_effect dst in
      let eff = eff_read (t_freepvs Spv.empty keep) in
      let ok, _, ex = sp_seq env e1 res xres out eff dst in
      let ne0 = sp_complete eff_empty a_gt_b dst in
      let ne1 = sp_havoc env e.e_effect res last dst in
      let src = dst_step_back e.e_effect e.e_effect dst in
      let hav = sp_havoc env e.e_effect res prev src in
      let adv = advancement src in
      let sbs = if Mexn.is_empty ex then Mvs.empty
                else Mvs.singleton v (t_var (clone_vs v)) in
      let ok = wp_forall [v] (sp_wp_close res hav adv ok) in
      let close sp = t_subst sbs (sp_sp_close res hav adv sp) in
      out_label e (wp_and init ok, sp_or ne0 ne1, Mexn.map close ex)

and sp_pred_let env e0 res xres out e1 eff dst =
  let eff1 = eff_bind_single (restore_pv res) e1.e_effect in
  let eff = eff_union_seq eff1 eff in
  sp_seq env e0 res xres out eff dst

and sp_pred_seq env e0 res xres out e1 eff dst =
  let eff = eff_union_seq e1.e_effect eff in
  sp_seq env e0 res xres out eff dst

and sp_seq env e res xres out eff dst = match e.e_node with
  | Eghost e1 ->
      sp_seq env (e_label_copy e e1) res xres out eff dst
  | Elet (LDvar ({pv_vs = v}, e0), e1)
  | Ecase (e0, [{pp_pat = {pat_node = Pvar v}}, e1]) ->
      let out = sp_seq env e1 res xres out eff dst in
      out_label e (sp_pred_let env e0 v xres out e1 eff dst)
  | Ecase (e0, [pp, e1]) when anon_pat pp ->
      let v = res_of_expr e0 in
      let out = sp_seq env e1 res xres out eff dst in
      out_label e (sp_pred_seq env e0 v xres out e1 eff dst)
  | Elet ((LDsym _| LDrec _) as ld, e1) ->
      let ok, ne, ex = sp_seq env e1 res xres out eff dst in
      let close_wp, close_sp = vc_let_sym env false ld e1 in
      out_label e (close_wp ok, close_sp ne, Mexn.map close_sp ex)
  | Eif (e0, e1, e2) when eff_pure e1.e_effect && eff_pure e2.e_effect ->
      let ok2, ne2, ex2 = out in
      let v, ok1, ne1 = sp_pure_if env e0.e_loc e1 e2 res in
      let ok = wp_and ok1 (sp_wp_close res ne1 Mvs.empty ok2) in
      let close sp = sp_sp_close res ne1 Mvs.empty sp in
      let ne = close ne2 and ex = Mexn.map close ex2 in
      let eff = eff_union_seq
        (eff_union_par e1.e_effect e2.e_effect) eff in
      out_label e (sp_seq env e0 v xres (ok,ne,ex) eff dst)
  | _ ->
      let ok2, ne2, ex2 = out in
      let dst' = dst_affected eff dst in
      let dst = dst_step_back e.e_effect eff dst in
      let ok1, ne1, ex1 = sp_expr env e res xres dst in
      let adv = advancement dst in
      let ok = wp_and ok1 (sp_wp_close res ne1 adv ok2) in
      let close sp = sp_sp_close res ne1 adv sp in
      let ex1 = if Mexn.is_empty ex1 then ex1 else
        Mexn.map (sp_adjust e.e_effect dst dst') ex1 in
      ok, close ne2, union_mexn ex1 (Mexn.map close ex2)

and sp_pure_if env loc e1 e2 res =
  let ok1, ne1, _ = sp_expr env e1 res Mexn.empty Mpv.empty in
  let ok2, ne2, _ = sp_expr env e2 res Mexn.empty Mpv.empty in
  (* we need a pvsymbol to prevent sp_wp_close from binding *)
  let v = create_pvsymbol (id_fresh ?loc "result") ity_bool in
  let test = t_equ (t_var v.pv_vs) t_bool_true in
  let ne = match term_of_post ~prop:false res ne1 with
    | Some (t1, f1) -> (* creative indentation ahead *)
          (match term_of_post ~prop:false res ne2 with
    | Some (t2, f2) ->
        let t = t_if_simp test t1 t2 in
        let f = t_if_simp test f1 f2 in
        sp_and (t_equ (t_var res) t) f
    | None -> t_if_simp test ne1 ne2)
    | None -> t_if_simp test ne1 ne2 in
  v.pv_vs, wp_if test ok1 ok2, ne

and vc_let_sym env vc_wp ld {e_effect = eff} =
  (* when we havoc the VC of a locally defined function,
     we must take into account every write in the following
     expression and ignore the resets, because the function
     may be executed before the resets. *)
  let eff = eff_write eff.eff_reads eff.eff_writes in
  (* compute the pre-condition *)
  let ok = match ld with
    | LDvar _ -> assert false (* not applicable *)
    | LDsym (_, {c_node = Capp _| Cpur _| Cany}) ->
        t_true
    | LDsym (_, {c_node = Cfun e; c_cty = cty}) ->
        wp_havoc env eff (vc_fun env vc_wp cty e)
    | LDrec rdl ->
        let wl = vc_rec env vc_wp rdl in
        wp_havoc env eff (List.fold_right wp_and wl t_true) in
  (* compute the post-condition, as in [Pdecl.create_let_decl] *)
  let cty_axiom cty f axms =
    if t_equal f t_true then axms else
    let p = sp_of_pre expl_pre cty.cty_pre in
    let args = List.map (fun v -> v.pv_vs) cty.cty_args in
    let f = wp_forall args (sp_implies p (bind_oldies cty f)) in
    wp_havoc env eff f :: axms in
  let add_rs sm s c (abst,axms) = match s.rs_logic with
    | RLls _ -> assert false
    | RLnone -> abst, axms
    | RLlemma ->
        let cty = c.c_cty in
        let r,q = wp_of_post expl_post cty.cty_result cty.cty_post in
        let f = if ty_equal r.vs_ty ty_unit
          then t_subst_single r t_void q
          else t_exists_close_simp [r] [] q in
        abst, cty_axiom cty f axms
    | RLpv v ->
        let c = if Mrs.is_empty sm then c else c_rs_subst sm c in
        let cty = match c.c_node with
          | Cany | Capp _ | Cpur _ -> c.c_cty
          | Cfun e ->
              let res = res_of_expr e in
              let prop = ity_equal e.e_ity ity_bool in
              let ql = match term_of_expr ~prop e with
                | Some f ->
                    let f = match f.t_node with
                      | Tapp (ps, [t; {t_node = Tapp (fs,[])}])
                        when ls_equal ps ps_equ && ls_equal fs fs_bool_true -> t
                      | _ -> f in
                    let q = match f.t_ty with
                      | None -> t_iff (t_equ (t_var res) t_bool_true) f
                      | Some _ -> t_equ (t_var res) f in
                    [create_post res q]
                | None when c.c_cty.cty_post = [] ->
                    begin match post_of_expr (t_var res) e with
                    | Some f -> [create_post res f]
                    | None -> [] end
                | None -> [] in
              cty_add_post c.c_cty ql in
        let ql = cty_exec_post cty in
        let q = sp_of_post None expl_post v.pv_vs ql in
        v.pv_vs :: abst, cty_axiom cty q axms in
  let vl, ax = match ld with
    | LDvar _ -> assert false (* not applicable *)
    | LDsym (s,c) -> add_rs Mrs.empty s c ([],[])
    | LDrec rdl ->
        let add_rd sm d = Mrs.add d.rec_rsym d.rec_sym sm in
        let sm = List.fold_left add_rd Mrs.empty rdl in
        let add_rd d dl = add_rs sm d.rec_sym d.rec_fun dl in
        List.fold_right add_rd rdl ([],[]) in
  (* TODO: switch to sp_*_close when it handles multiple results *)
  let close_wp wp =
    wp_and ok (wp_forall vl (List.fold_right sp_implies ax wp)) in
  let close_sp = if vc_wp then (fun _ -> assert false) else
    (* replace pv with fresh vs so that sp_wp_close binds them *)
    let sbs = List.fold_left (fun sbs v ->
      Mvs.add v (t_var (clone_vs v)) sbs) Mvs.empty vl in
    fun sp -> t_subst sbs (List.fold_right sp_and ax sp) in
  close_wp, close_sp

and vc_cexp env ?(o2n=Mvs.empty) vc_wp c = match c.c_node with
  | Cfun e -> vc_fun ~o2n env vc_wp c.c_cty e
  | Capp _ | Cpur _ | Cany -> t_true

and vc_fun env ?(o2n=Mvs.empty) vc_wp c e =
  let p = sp_of_pre expl_pre c.cty_pre in
  let args = List.map (fun v -> v.pv_vs) c.cty_args in
  let mk_xq xs xq = wp_of_post expl_xpost xs.xs_ity xq in
  let r,q = wp_of_post expl_post c.cty_result c.cty_post in
  let e = if vc_wp || Slab.mem wp_label e.e_label
          then e else e_label_add sp_label e in
  let w = wp_expr env e r q (Mexn.mapi mk_xq c.cty_xpost) in
  wp_forall args (sp_implies p (t_subst o2n (bind_oldies c w)))

and vc_rec ({letrec_ps = lps} as env) vc_wp rdl =
  let vc_rd {rec_fun = c; rec_varl = varl} =
    if varl = [] then vc_cexp env vc_wp c else
    let o2n, varl = oldify_variant varl in
    let add lps rd = let decr = ls_decr_of_rec_defn rd in
      Mls.add (Opt.get decr) (varl, List.map snd rd.rec_varl) lps in
    let env = { env with letrec_ps = List.fold_left add lps rdl } in
    vc_cexp env ~o2n vc_wp c in
  List.map vc_rd rdl

let mk_vc_decl kn id f =
  let {id_string = nm; id_label = label; id_loc = loc} = id in
  let label = if lab_has_expl label then label else
    Slab.add (Ident.create_label ("expl:VC for " ^ nm)) label in
  let pr = create_prsymbol (id_fresh ~label ?loc ("VC " ^ nm)) in
  let f = wp_forall (Mvs.keys (t_freevars Mvs.empty f)) f in
  let f = if Debug.test_flag no_eval then f else
    Eval_match.eval_match kn f in
  create_pure_decl (create_prop_decl Pgoal pr f)

let vc env kn d = match d.pd_node with
  | PDlet (LDsym (s, {c_node = Cfun e; c_cty = cty})) ->
      let env = mk_env env kn in
      let f = vc_fun env (Debug.test_noflag debug_sp) cty e in
      [mk_vc_decl kn s.rs_name f]
  | PDlet (LDrec rdl) ->
      let env = mk_env env kn in
      let fl = vc_rec env (Debug.test_noflag debug_sp) rdl in
      List.map2 (fun rd f -> mk_vc_decl kn rd.rec_sym.rs_name f) rdl fl
  | _ -> []
