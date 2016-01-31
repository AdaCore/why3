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

let _ity_of_vs v = (restore_pv v).pv_ity

let new_of_vs v = create_vsymbol (id_clone v.vs_name) v.vs_ty

let new_of_pv v = new_of_vs v.pv_vs

let vs_result ity = create_vsymbol (id_fresh "result") (ty_of_ity ity)

(* explanations *)

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

let vc_expl l f =
  let f = if Slab.mem Term.stop_split f.t_label
    then f else t_label_add Term.stop_split f in
  if lab_has_expl f.t_label then f else t_label_add l f

(* propositional connectives with limited simplification *)

(*
let can_simp t = not (Slab.mem stop_split t.t_label)

let vc_and f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _ when can_simp f1 -> f2
  | _, Ttrue when can_simp f2 -> t_label_remove asym_split f1
  | _, _ -> t_and f1 f2

let vc_and_asym f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _ when can_simp f1 -> f2
  | _, Ttrue when can_simp f2 -> t_label_remove asym_split f1
  | _, _ -> t_and_asym f1 f2

let vc_or f1 f2 = match f1.t_node, f2.t_node with
  | Tfalse, _ when can_simp f1 -> f2
  | _, Tfalse when can_simp f2 -> t_label_remove asym_split f1
  | _, _ -> t_or f1 f2
*)

let vc_implies f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _ | _, Ttrue -> f2
  | _, _ -> t_implies f1 f2

let vc_implies_pre fl f = List.fold_right vc_implies fl f

let vc_implies_post fl v f = let t = t_var v in
  let implies q f = vc_implies (open_post_with t q) f in
  List.fold_right implies fl f

let vc_forall vl f = t_forall_close_simp vl [] f

let vc_let v t f = t_let_close_simp v t f

(*
type defn_fmla =
  | DFdefn of term
  | DFfmla of term
  | DFdffm of term * term

let df_atom v f = match f.t_node with
  | Tapp (ps, [{t_node = Tvar u}; t])
    when ls_equal ps ps_equ && vs_equal u v && t_v_occurs v t = 0 ->
         DFdefn t
  | _ -> DFfmla f

let df_and_left df1 f2 = match df1 with
  | DFdefn t -> DFdffm (t, f2)
  | DFfmla f1 -> DFfmla (t_and f1 f2)
  | DFdffm (t,f1) -> DFdffm (t, t_and f1 f2)

let df_and_right f1 df2 = match df2 with
  | DFdefn t -> DFdffm (t, f1)
  | DFfmla f2 -> DFfmla (t_and f1 f2)
  | DFdffm (t,f2) -> DFdffm (t, t_and f1 f2)

let df_implies df1 f2 = match df1 with
  | DFdefn t -> DFdffm (t, f2)
  | DFfmla f1 -> DFfmla (t_implies f1 f2)
  | DFdffm (t,f1) -> DFdffm (t, t_implies f1 f2)

let df_forall v df1 f2 = match df1 with
  | DFdefn t -> t_let_close_simp v t f2
  | DFfmla f1 -> t_forall_close_simp [v] [] (t_implies f1 f2)
  | DFfmla (t,f1) -> t_let_close_simp v t (t_implies f1 f2)

let df_label_copy e df = match df with
  | DFdefn _ -> df
  | DFfmla f -> DFfmla (t_label_copy e f)
  | DFdffm (t,f) -> DFdffm (t, t_label_copy e f)

let vc_forall_post v p f =
  (* we optimize for the case when a postcondition
     is of the form (... /\ result = t /\ ...) *)
  let rec down p = match p.t_node with
    | Tbinop (Tand,f1,f2) ->
        df_label_copy p (match down f1 with
          | DFfmla f1 -> df_and_right f1 (down f2)
          | df1 -> df_and_left df1 f2)
    | _ -> df_atom v p in
  if ty_equal v.vs_ty ty_unit then
    t_subst_single v t_void (t_implies p f)
  else df_forall v (down p) f

let t_and_subst v t1 t2 =
  (* if [t1] defines variable [v], return [t2] with [v] replaced by its
     definition. Otherwise return [t1 /\ t2] *)
  match is_equality_for v t1 with
  | Some t -> t_subst_single v t t2
  | None -> t_and t1 t2

let t_implies_subst v t1 t2 =
  (* if [t1] defines variable [v], return [t2] with [v] replaced by its
     definition. Otherwise return [t1 -> t2] *)
  match is_equality_for v t1 with
  | Some t -> t_subst_single v t t2
  | None -> t_implies_simp t1 t2

let open_unit_post q =
  let v, q = open_post q in
  t_subst_single v t_void q

let create_unit_post =
  let v = create_vsymbol (id_fresh "void") ty_unit in
  fun q -> create_post v q

let vs_result e =
  create_vsymbol (id_fresh ?loc:e.e_loc "result") (ty_of_ity e.e_ity)
*)

(* VCgen environment *)

type vc_env = {
  known_map : Pdecl.known_map;
  ps_int_le : Term.lsymbol;
  ps_int_ge : Term.lsymbol;
  ps_int_lt : Term.lsymbol;
  ps_int_gt : Term.lsymbol;
  fs_int_pl : Term.lsymbol;
  fs_int_mn : Term.lsymbol;
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

(* a type is affected if a modified region is reachable from it *)

let _reg_affected wr reg = Util.any reg_rch_fold (Mreg.contains wr) reg
let ity_affected wr ity = Util.any ity_rch_fold (Mreg.contains wr) ity

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

(* produce a rebuilding postcondition after a write effect *)

type 'a nested_list =
  | NLflat of 'a nested_list list
  | NLcons of 'a * 'a nested_list
  | NLnil

let rec nl_flatten nl acc = match nl with
  | NLflat l -> List.fold_right nl_flatten l acc
  | NLcons (elm, nl) -> elm :: nl_flatten nl acc
  | NLnil -> acc

let rec nl_implies nl f = match nl with
  | NLflat l -> List.fold_right nl_implies l f
  | NLcons (elm, nl) -> vc_implies elm (nl_implies nl f)
  | NLnil -> f

let cons_t_simp nt t fl =
  if t_equal nt t then fl else NLcons (t_equ nt t, fl)

let rec havoc kn wr mreg t ity =
  if not (ity_affected wr ity) then t, NLnil else
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg ({reg_its = s} as r) when s.its_nonfree || Mreg.mem r wr ->
      let itd = find_its_defn kn s in
      let isb = its_match_regs s r.reg_args r.reg_regs in
      let wfs = Mreg.find_def Mpv.empty r wr in
      let nt = Mreg.find r mreg in
      let field rs =
        if Mpv.mem (Opt.get rs.rs_field) wfs then NLnil else
        let ity = ity_full_inst isb rs.rs_cty.cty_result in
        let ls = ls_of_rs rs and ty = Some (ty_of_ity ity) in
        let t = t_app ls [t] ty and nt = t_app ls [nt] ty in
        let t, fl = havoc kn wr mreg t ity in
        cons_t_simp nt t fl in
      nt, NLflat (List.map field itd.itd_fields)
  | Ityreg {reg_its = s; reg_args = tl; reg_regs = rl}
  | Ityapp (s,tl,rl) ->
      let itd = find_its_defn kn s in
      let isb = its_match_regs s tl rl in
      begin match itd.itd_constructors with
      | [{rs_logic = RLls cs}] (* record *)
        when List.length cs.ls_args = List.length itd.itd_fields ->
          let field rs =
            let ity = ity_full_inst isb rs.rs_cty.cty_result in
            havoc kn wr mreg (t_app_infer (ls_of_rs rs) [t]) ity in
          let tl, fl = List.split (List.map field itd.itd_fields) in
          let t0 = match tl with
            | {t_node = Tapp (_,[t])}::_ -> t | _ -> t_false in
          let triv rs t = match t.t_node with
            | Tapp (s,[t]) -> ls_equal s (ls_of_rs rs) && t_equal t t0
            | _ -> false in
          let t = if List.for_all2 triv itd.itd_fields tl
            then t0 else fs_app cs tl (ty_of_ity ity) in
          t, NLflat fl
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
            let get_hv v ity = havoc kn wr mreg (t_var v) ity in
            let tl, fl = List.split (List.map2 get_hv vl ityl) in
            let fl = List.fold_right nl_flatten fl [] in
            (p, fs_app cs tl ty), (p, t_and_simp_l fl) in
          let tbl, fbl = List.split (List.map branch cl) in
          let t = t_case_close t tbl and f = t_case_close_simp t fbl in
          t, if t_equal f t_true then NLnil else NLcons (f, NLnil)
      end

let print_mpv mpv = if Debug.test_flag debug then
  Format.printf "@[vars = %a@]@." (Pp.print_list Pp.space
    (fun fmt (o,n) -> Format.fprintf fmt "(%a -> %a)"
      Ity.print_pv o Pretty.print_vs n)) (Mpv.bindings mpv)

let print_mreg mreg = if Debug.test_flag debug then
  Format.printf "@[regs = %a@]@." (Pp.print_list Pp.space
    (fun fmt (r,t) -> Format.fprintf fmt "(%a -> %a)"
      Ity.print_reg r Pretty.print_term t)) (Mreg.bindings mreg)

let _havoc_fast {known_map = kn} {eff_writes = wr; eff_covers = cv} mpv =
  if Sreg.is_empty cv || Mpv.is_empty mpv then [] else
  let mreg = name_regions kn cv mpv in
  let () = print_mpv mpv; print_mreg mreg in
  let update {pv_vs = o; pv_ity = ity} n acc =
    let t, fl = havoc kn wr mreg (t_var o) ity in
    nl_flatten (cons_t_simp (t_var n) t fl) acc in
  Mpv.fold update mpv []

let havoc_slow {known_map = kn} {eff_writes = wr; eff_covers = cv} w =
  if Sreg.is_empty cv then w else
  let fvs = t_freevars Mvs.empty w in
  let add v _ m = let pv = restore_pv v in
    if ity_affected cv pv.pv_ity then
    Mpv.add pv (new_of_vs v) m else m in
  let mpv = Mvs.fold add fvs Mpv.empty in
  if Mpv.is_empty mpv then w else
  let mreg = name_regions kn cv mpv in
  let () = print_mpv mpv; print_mreg mreg in
  let add _ t fvs = t_freevars fvs t in
  let fvs = Mreg.fold add mreg Mvs.empty in
  let update {pv_vs = o; pv_ity = ity} n w =
    let t, fl = havoc kn wr mreg (t_var o) ity in
    if Mvs.mem n fvs then
      nl_implies (cons_t_simp (t_var n) t fl) w
    else vc_let n t (nl_implies fl w) in
  let add o n sbs = Mvs.add o.pv_vs (t_var n) sbs in
  let w = t_subst (Mpv.fold add mpv Mvs.empty) w in
  vc_forall (Mvs.keys fvs) (Mpv.fold update mpv w)

let _step_back wr1 rd2 wr2 mpv =
  if Mreg.is_empty wr1 then Mpv.empty else
  let back o n =
    if not (ity_affected wr1 o.pv_ity) then None else
    if not (ity_affected wr2 o.pv_ity) then Some n else
    Some (new_of_pv o) in
  let mpv = Mpv.mapi_filter back mpv in
  let add v acc =
    if Mpv.mem v mpv || not (ity_affected wr1 v.pv_ity)
    then acc else Mpv.add v (new_of_pv v) acc in
  Spv.fold add rd2 mpv

(* classical WP *)

let ok_of_post l ity = function
  | q::ql ->
      let v, q = open_post q in let t = t_var v in
      let mk_post q = vc_expl l (open_post_with t q) in
      v, t_and_l (vc_expl l q :: List.map mk_post ql)
  | [] ->
      vs_result ity, t_true

let bind_oldies c f = Mpv.fold (fun o v f ->
  t_subst_single o.pv_vs (t_var v.pv_vs) f) c.cty_oldies f

let rec slow env e res q xq = match e.e_node with
  | Evar v ->
      t_subst_single res (vc_label e (t_var v.pv_vs)) q
  | Econst c ->
      t_subst_single res (vc_label e (t_const c)) q

  | Eexec ({c_node = Cfun _} as _c) ->
      assert false (* TODO *)
  | Eexec ({c_cty = {cty_args = _::_}} as _c) ->
      assert false (* TODO *)

  | Eexec {c_cty = {cty_args = []} as c} ->
      (* TODO: rewrite c.cty_post wrt c.cty_args <> [] *)
      (* TODO: vc_forall_post *)
      let q = vc_forall [res] (vc_implies_post c.cty_post res q) in
      let xq = Mexn.set_inter xq c.cty_effect.eff_raises in
      let xq_implies _ (v,q) l = Some (v, vc_implies_post l v q) in
      let xq = Mexn.diff xq_implies xq c.cty_xpost in
      let xq_and _ (v,q) f = t_and f (vc_forall [v] q) in
      let q = Mexn.fold xq_and xq q in
      let q = havoc_slow env c.cty_effect q in
      let q = bind_oldies c q in (* TODO: cty_args <> [] *)
      let vl = List.map (fun v -> v.pv_vs) c.cty_args in
      let and_pre f q =
        (* TODO: handle recursive calls *)
        t_and (vc_expl expl_pre (vc_forall vl f)) q in
      vc_label e (List.fold_right and_pre c.cty_pre q)

  | Elet (LDvar (v, e1), e2) (* FIXME: do we need this? *)
    when Slab.mem proxy_label v.pv_vs.vs_name.id_label ->
    (* we push the label down, past the inserted "let" *)
      let q = slow env (e_label_copy e e2) res q xq in
      slow env e1 v.pv_vs q xq
  | Elet (LDvar (v, e1), e2) ->
      let q = slow env e2 res q xq in
      vc_label e (slow env e1 v.pv_vs q xq)
  | Eif (e1, e2, e3) ->
      let v = vs_result e1.e_ity in
      let test = t_equ (t_var v) t_bool_true in
      (* TODO: how should we handle prop-behind-bool-typed exprs? *)
      (* TODO: handle e_true and e_false, restore /\ and \/ *)
(* FIXME: wrong if e2 or e3 have preconditions depending on test
      let q = if eff_pure e2.e_effect && eff_pure e3.e_effect then
        let u2 = vs_result e2.e_ity and u3 = vs_result e3.e_ity in
        let r = t_subst_single res (t_if test (t_var u2) (t_var u3)) q in
        slow env e2 u2 (slow env e3 u3 (t_subst_single res r q) xq) xq
      else
*)
      let q = t_if test (slow env e2 res q xq) (slow env e3 res q xq) in
      vc_label e (slow env e1 v q xq)
  | _ -> assert false (* TODO *)

and vc_fun env c e =
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
  let r,q = ok_of_post expl_post c.cty_result c.cty_post in
  let mk_xq xs xq = ok_of_post expl_xpost xs.xs_ity xq in
  let f = slow env e r q (Mexn.mapi mk_xq c.cty_xpost) in
  let f = vc_implies_pre c.cty_pre (bind_oldies c f) in
  vc_forall args f

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
      let f = t_and_simp_l (havoc_fast kn eff mpv) in
      let fvs = Mvs.domain (t_freevars Mvs.empty f) in
      let f = t_forall_close (Svs.elements fvs) [] f in
      let pr = create_prsymbol (id_fresh (s.rs_name.id_string ^ "_havoc")) in
      [create_pure_decl (create_prop_decl Pgoal pr f)]
  | _ -> []
*)
