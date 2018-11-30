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

open Wstdlib
open Ident
open Ty
open Term
open Decl
open Ity
open Expr
open Pdecl

(* basic tools *)

let debug_vc = Debug.register_info_flag "vc_debug"
  ~desc:"Print@ details@ of@ verification@ conditions@ generation."

let debug_reflow = Debug.register_info_flag "vc_reflow"
  ~desc:"Debug@ elimination@ of@ the@ dead@ code@ in@ VC."

let debug_sp = Debug.register_flag "vc_sp"
  ~desc:"Use@ 'Efficient@ Weakest@ Preconditions'@ for@ verification."

let debug_no_eval = Debug.register_flag "vc_no_eval"
  ~desc:"Do@ not@ simplify@ pattern@ matching@ on@ record@ datatypes@ in@ VCs."

let debug_ignore_diverges = Debug.register_info_flag "ignore_missing_diverges"
  ~desc:"Suppress@ warnings@ on@ missing@ diverges."

let case_split = Ident.create_attribute "case_split"
let add_case t = t_attr_add case_split t

let clone_pv loc {pv_vs = {vs_name = id; vs_ty = ty}} =
  (* we do not preserve the location of the initial pv
     in the new variable for SP, because we do not want
     to require a model for it and rely on "model_vc_*"
     attributes to produce new, correctly located, variables *)
  let id = id_fresh ~attrs:id.id_attrs ?loc id.id_string in
  create_vsymbol id ty

let pv_is_unit v = ity_equal v.pv_ity ity_unit

let pv_of_ity s ity = create_pvsymbol (id_fresh s) ity

let res_of_post ity = function
  | q::_ -> create_pvsymbol (clone_post_result q) ity
  | _ -> pv_of_ity "result" ity

let res_of_cty cty = res_of_post cty.cty_result cty.cty_post

let proxy_of_expr =
  let attrs = Sattr.singleton proxy_attr in fun e ->
  let id = id_fresh ?loc:e.e_loc ~attrs "o" in
  create_pvsymbol id e.e_ity

let sp_attr = Ident.create_attribute "vc:sp"
let wp_attr = Ident.create_attribute "vc:wp"
let wb_attr = Ident.create_attribute "vc:white_box"
let kp_attr = Ident.create_attribute "vc:keep_precondition"
let nt_attr = Ident.create_attribute "vc:divergent"

let vc_attrs =
  Sattr.add nt_attr (Sattr.add kp_attr (Sattr.add wb_attr
  (Sattr.add sp_attr (Sattr.add wp_attr Sattr.empty))))

(* VCgen environment *)

type vc_env = {
  known_map : Pdecl.known_map;
  ts_ranges : Theory.tdecl Mts.t;
  ps_int_le : lsymbol;
  ps_int_ge : lsymbol;
  ps_int_lt : lsymbol;
  ps_int_gt : lsymbol;
  fs_int_pl : lsymbol;
  fs_int_mn : lsymbol;
  ps_wf_acc : lsymbol;
  exn_count : int ref;
  divergent : bool;
}

let mk_env {Theory.th_export = ns_int} {Theory.th_export = ns_acc} kn tuc = {
  known_map = kn;
  ts_ranges = tuc.Theory.uc_ranges;
  ps_int_le = Theory.ns_find_ls ns_int [Ident.op_infix "<="];
  ps_int_ge = Theory.ns_find_ls ns_int [Ident.op_infix ">="];
  ps_int_lt = Theory.ns_find_ls ns_int [Ident.op_infix "<"];
  ps_int_gt = Theory.ns_find_ls ns_int [Ident.op_infix ">"];
  fs_int_pl = Theory.ns_find_ls ns_int [Ident.op_infix "+"];
  fs_int_mn = Theory.ns_find_ls ns_int [Ident.op_infix "-"];
  ps_wf_acc = Theory.ns_find_ls ns_acc ["acc"];
  exn_count = ref 0;
  divergent = false;
}

let acc env r t =
  let ps = env.ps_wf_acc in
  if not (Mid.mem ps.ls_name env.known_map) then
    Loc.errorm ?loc:t.t_loc "please import relations.WellFounded";
  let ty = t_type t in
  let r = t_closure r [ty; ty] None in
  ps_app ps [r; t]

(* every exception-catching clause is represented by
   a unique integer, so that we can move code inside
   try-with expressions without capturing exceptions *)
let new_exn env = incr env.exn_count; !(env.exn_count)

(* FIXME: cannot verify int.why because of a cyclic dependency.
   int.Int is used for the "for" loops and for integer variants.
   We should be able to extract the necessary lsymbols from kn. *)
let mk_env env kn tuc =
  let th_int = Env.read_theory env ["int"] "Int" in
  let th_wf  = Env.read_theory env ["relations"] "WellFounded" in
  mk_env th_int th_wf kn tuc

let int_of_range env ty =
  let td = Mts.find ty env.ts_ranges in
  match td.Theory.td_node with
  | Theory.Meta (_, [_; Theory.MAls s]) -> s
  | _ -> assert false

(* explanation attributes *)

let expl_pre       = Ident.create_attribute "expl:precondition"
let expl_post      = Ident.create_attribute "expl:postcondition"
let expl_xpost     = Ident.create_attribute "expl:exceptional postcondition"
let expl_assume    = Ident.create_attribute "expl:assumption"
let expl_assert    = Ident.create_attribute "expl:assertion"
let expl_check     = Ident.create_attribute "expl:check"
let expl_lemma     = Ident.create_attribute "expl:lemma"
let expl_absurd    = Ident.create_attribute "expl:unreachable point"
let expl_for_bound = Ident.create_attribute "expl:loop bounds"
let expl_off_bound = Ident.create_attribute "expl:out of loop bounds"
let expl_loop_init = Ident.create_attribute "expl:loop invariant init"
let expl_loop_keep = Ident.create_attribute "expl:loop invariant preservation"
let expl_loop_vari = Ident.create_attribute "expl:loop variant decrease"
let expl_variant   = Ident.create_attribute "expl:variant decrease"
let expl_type_inv  = Ident.create_attribute "expl:type invariant"
let expl_divergent = Ident.create_attribute "expl:termination"

let attrs_has_expl attrs =
  Sattr.exists (fun a -> Strings.has_prefix "expl:" a.attr_string) attrs

let annot_attrs = Sattr.add stop_split (Sattr.singleton annot_attr)

let vc_expl loc attrs expl f =
  let attrs = Sattr.union annot_attrs (Sattr.union attrs f.t_attrs) in
  let attrs = if attrs_has_expl attrs then attrs else Sattr.add expl attrs in
  t_attr_set ?loc:(if loc = None then f.t_loc else loc) attrs f

(* propositional connectives with limited simplification *)

let sp_implies sp wp = match sp.t_node, wp.t_node with
  | Ttrue, _ | _, Ttrue -> wp
  | _, _ -> t_implies sp wp

let sp_or sp1 sp2 = match sp1.t_node, sp2.t_node with
  | Ttrue, _ | _, Tfalse -> sp1
  | _, Ttrue | Tfalse, _ -> sp2
  | _, _ -> add_case (t_or sp1 sp2)

let sp_and sp1 sp2 = match sp1.t_node, sp2.t_node with
  | Ttrue, _ | _, Tfalse -> sp2
  | _, Ttrue | Tfalse, _ -> sp1
  | _, _ -> t_and sp1 sp2

(* sp_or adds "case_split", so we avoid using it here *)
let sp_if c sp1 sp2 = match c.t_node, sp1.t_node, sp2.t_node with
  | Ttrue, _, _  | _, Ttrue,  Ttrue  -> sp1
  | Tfalse, _, _ | _, Tfalse, Tfalse -> sp2
  | _, _, Tfalse -> sp_and c sp1
  | _, Tfalse, _ -> sp_and (t_not_simp c) sp2
  | _, Ttrue, _  -> t_or c sp2
  | _, _, Ttrue  -> t_or (t_not_simp c) sp1
  | _, _, _ -> add_case (t_if c sp1 sp2)

let sp_case t bl =
  let isfalse b = match t_open_branch b with
    | _, { t_node = Tfalse } -> true | _ -> false in
  if List.for_all isfalse bl then t_false else add_case (t_case t bl)

let can_simp wp = match wp.t_node with
  | Ttrue -> not (Sattr.mem annot_attr wp.t_attrs)
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
  | _, _, Ttrue  when can_simp wp2 -> sp_implies c wp1
  | _, Ttrue, _  when can_simp wp1 -> sp_implies (t_not_simp c) wp2
  | _, _, _ -> t_if c wp1 wp2

let wp_case t bl =
  let check b = can_simp (snd (t_open_branch b)) in
  if List.for_all check bl then t_true else t_case t bl

let wp_forall vl wp = t_forall_close_simp vl [] wp
let sp_exists vl sp = t_exists_close_simp vl [] sp

let wp_let v t wp =
  if pv_is_unit v then t_subst_single v.pv_vs t_void wp
                  else t_let_close_simp v.pv_vs t wp

let sp_let v t sp rd =
  if pv_is_unit v then t_subst_single v.pv_vs t_void sp else
  if Spv.mem v rd then sp_and (t_equ (t_var v.pv_vs) t) sp else
  t_let_close_simp v.pv_vs t sp

(* variant decrease preconditions *)

let decrease_alg env loc old_t t =
  let oty = t_type old_t and nty = t_type t in
  let quit () = Loc.errorm ?loc "no default order for %a" Pretty.print_ty nty in
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
  let ty = t_type t in
  if ty_equal (t_type old_t) ty then
    match ty.ty_node with
    | Tyapp (ts,_) when ts_equal ts ts_int ->
        t_and (ps_app env.ps_int_le [t_nat_const 0; old_t])
              (ps_app env.ps_int_lt [t; old_t])
    | Tyapp (ts, _) when is_range_type_def ts.ts_def ->
        let ls = int_of_range env ts in
        let proj t = fs_app ls [t] ty_int in
        ps_app env.ps_int_lt [proj t; proj old_t]
    | _ ->
        decrease_alg env loc old_t t
  else decrease_alg env loc old_t t

let decrease env loc attrs expl olds news =
  if olds = [] && news = [] then t_true else
  let rec decr olds news = match olds, news with
    | (old_t, Some old_r)::olds, (t, Some r)::news when ls_equal old_r r ->
        if t_equal old_t t then decr olds news else
        let dt = t_and (ps_app r [t; old_t]) (acc env r old_t) in
        t_or_simp dt (t_and_simp (t_equ old_t t) (decr olds news))
    | (old_t, None)::olds, (t, None)::news when oty_equal old_t.t_ty t.t_ty ->
        if t_equal old_t t then decr olds news else
        let dt = decrease_def env loc old_t t in
        t_or_simp dt (t_and_simp (t_equ old_t t) (decr olds news))
    | (old_t, None)::_, (t, None)::_ ->
        decrease_def env loc old_t t
    | _::_, [] -> t_true
    | _ -> t_false in
  vc_expl loc attrs expl (decr olds news)

let old_of_pv {pv_vs = v; pv_ity = ity} =
  create_pvsymbol (id_clone v.vs_name) (ity_purify ity)

let oldify_variant varl =
  let fpv = Mpv.mapi_filter (fun v _ -> (* oldify mutable vars *)
    if v.pv_ity.ity_pure then None else Some (old_of_pv v))
    (List.fold_left (fun s (t,_) -> t_freepvs s t) Spv.empty varl) in
  if Mpv.is_empty fpv then Mpv.empty, varl else
  let o2v = Mpv.fold (fun v o s -> Mpv.add o v s) fpv Mpv.empty in
  let v2o = Mpv.fold (fun v o s ->
    Mvs.add v.pv_vs (t_var o.pv_vs) s) fpv Mvs.empty in
  o2v, List.map (fun (t,r) -> t_subst v2o t, r) varl

let renew_oldies o2v =
  let renew o v (n2v, o2n) = let n = old_of_pv v in
    Mpv.add n v n2v, Mvs.add o.pv_vs (t_var n.pv_vs) o2n in
  Mpv.fold renew o2v (Mpv.empty, Mvs.empty)

(* convert user specifications into goals (wp) and premises (sp) *)

let wp_of_inv loc attrs expl pl =
  t_and_asym_l (List.map (vc_expl loc attrs expl) pl)

let wp_of_pre loc attrs pl = wp_of_inv loc attrs expl_pre pl

let wp_of_post expl ity ql =
  let v = res_of_post ity ql in let t = t_var v.pv_vs in
  let make q = vc_expl None Sattr.empty expl (open_post_with t q) in
  v, t_and_asym_l (List.map make ql)

let push_stop loc attrs expl f =
  let rec push f = match f.t_node with
    | Tbinop (Tand,g,h)
      when not (Sattr.mem annot_attr f.t_attrs) ->
        t_attr_copy f (t_and (push g) (push h))
    | _ -> vc_expl loc attrs expl f in
  push f

let sp_of_inv loc attrs expl pl =
  t_and_l (List.map (push_stop loc attrs expl) pl)

let sp_of_pre pl = sp_of_inv None Sattr.empty expl_pre pl

let sp_of_post loc attrs expl v ql = let t = t_var v.pv_vs in
  let push q = push_stop loc attrs expl (open_post_with t q) in
  t_and_l (List.map push ql)

(* definitions of local let-functions are inserted in the VC
   as premises for the subsequent code (in the same way as
   definitions of top-level let-functions are translated to
   logical definitions in Pdecl.create_let_decl) *)
let cty_enrich_post c = match c with
  | {c_node = Cfun e; c_cty = cty} ->
      let {pv_vs = u} = res_of_cty cty in
      let prop = ty_equal u.vs_ty ty_bool in
      begin match term_of_expr ~prop e with
      | Some f ->
          let f = match f.t_node with
            | Tapp (ps, [t; {t_node = Tapp (fs,[])}])
              when ls_equal ps ps_equ
                && ls_equal fs fs_bool_true -> t
            | _ -> f in
          let q = match f.t_ty with
            | None -> t_iff (t_equ (t_var u) t_bool_true) f
            | Some _ -> t_equ (t_var u) f in
          cty_add_post cty [create_post u q]
      | None when cty.cty_post = [] ->
          begin match post_of_expr (t_var u) e with
          | Some f -> cty_add_post cty [create_post u f]
          | None -> cty end
      | None -> cty end
  | _ -> c.c_cty

(* k-expressions: simplified code *)

type ktag = WP | SP | Out of bool Mint.t | Push of bool | Off of attribute

type kode =
  | Kseq   of kode * int * kode           (* 0: sequence, N: try-with *)
  | Kpar   of kode * kode                 (* non-deterministic choice *)
  | Kif    of pvsymbol * kode * kode          (* deterministic choice *)
  | Kcase  of pvsymbol * (pattern * kode) list    (* pattern matching *)
  | Khavoc of pvsymbol option Mpv.t Mreg.t *
              Loc.position option           (* writes and assignments *)
  | Klet   of pvsymbol * term * term         (* let v = t such that f *)
  | Kval   of pvsymbol list * term        (* let vl = any such that f *)
  | Kcut   of term                        (* assert: check and assume *)
  | Kstop  of term                        (* check and halt execution *)
  | Kcont  of int                                (* 0: skip, N: raise *)
  | Kaxiom of kode                  (* axiom-functions: assume the VC *)
  | Ktag   of ktag * kode          (* switch VCgen or mark to push up *)

(* kode requires, and expr provides, the following invariants:
   - a used variable must be defined by Klet or declared by Kval
     on every codepath leading to its use, and only once
   - in Klet(v,t,_), variable v does not occur in term t
   - every visible variable is a pvsymbol *)

let rec k_print fmt k = match k with
  | Kseq (k1 ,0, k2) -> Format.fprintf fmt
      "@[%a;@\n%a@]" k_print k1 k_print k2
  | Kseq (k1, i, k2) -> Format.fprintf fmt
      "@[TRY %a@\n%d : %a@]" k_print k1 i k_print k2
  | Kpar (Kstop f, k2) -> Format.fprintf fmt
      "@[@[<hov 4>CHECK %a@];@\n%a@]" Pretty.print_term f k_print k2
  | Kpar (k1, k2) -> Format.fprintf fmt
      "@[[ @[%a@]@\n| @[%a@] ]@]" k_print k1 k_print k2
  | Kif (v, k1, k2) -> Format.fprintf fmt
      "@[IF %a@\nTHEN %a@\nELSE %a@]"
        Ity.print_pv v k_print k1 k_print k2
  | Kcase (v, bl) ->
      let branch fmt (p,k) = Format.fprintf fmt
        "@[<hov 4>| %a ->@ %a@]" Pretty.print_pat p k_print k in
      Format.fprintf fmt "@[CASE %a\n@[%a@]@]"
        Ity.print_pv v (Pp.print_list Pp.newline branch) bl
  | Khavoc _ -> Format.fprintf fmt "HAVOC" (* TODO *)
  | Klet (v, t, {t_node = Ttrue}) -> Format.fprintf fmt
      "@[<hov 4>LET %a = %a@]" Ity.print_pv v Pretty.print_term t
  | Klet (v,t,f) -> Format.fprintf fmt
      "@[<hov 4>LET %a = %a WITH@ %a@]" Ity.print_pv v
        Pretty.print_term t Pretty.print_term f
  | Kval (vl,{t_node = Ttrue}) -> Format.fprintf fmt
      "@[<hov 4>VAL %a@]" (Pp.print_list Pp.space Ity.print_pv) vl
  | Kval (vl,f) -> Format.fprintf fmt
      "@[<hov 4>VAL %a WITH@ %a@]"
        (Pp.print_list Pp.space Ity.print_pv) vl Pretty.print_term f
  | Kcut f -> Format.fprintf fmt
      "@[<hov 4>ASSERT %a@]" Pretty.print_term f
  | Kstop f -> Format.fprintf fmt
      "@[<hov 4>STOP %a@]" Pretty.print_term f
  | Kcont 0 -> Format.fprintf fmt "SKIP"
  | Kcont i -> Format.fprintf fmt "RAISE %d" i
  | Kaxiom k -> Format.fprintf fmt "@[<hov 4>AXIOM %a@]" k_print k
  | Ktag (WP, k) -> Format.fprintf fmt "@[<hov 4>WP %a@]" k_print k
  | Ktag (SP, k) -> Format.fprintf fmt "@[<hov 4>SP %a@]" k_print k
  | Ktag (Out out, k) -> Format.fprintf fmt "@[<hov 4>OUT %a %a@]"
      (Pp.print_list Pp.space Pp.int) (Mint.keys out) k_print k
  | Ktag (Push cl, k) -> Format.fprintf fmt "@[<hov 4>PUSH %s %a@]"
      (if cl then "CLOSED" else "OPEN") k_print k
  | Ktag (Off attr, k) -> Format.fprintf fmt "@[<hov 4>OFF %s %a@]"
      attr.attr_string k_print k

(* check if a pure k-expression can be converted to a term.
   We need this for simple conjunctions, disjunctions, and
   pattern-matching exprs, to avoid considering each branch
   separately; also to have a single substitutable term. *)
let term_of_kode res k =
  let rec get_stack st k = match k with
    | Klet (v, t, f) when pv_equal v res -> st, Some (t, f), 0, Kcont 0
    | Klet (v, t, _) -> (v, Some t) :: st, None, 0, k
    | Kval (vl, _) ->
        let none v = if pv_is_unit v then Some t_void else None in
        List.fold_left (fun st v -> (v, none v) :: st) st vl, None, 0, k
    | Kcut _ | Kaxiom _ -> st, None, 0, k
    | Kcont i -> st, None, i, k
    | Kseq (k1, i, k2) ->
        let st, d, j, k1 = get_stack st k1 in
        if i <> j then st, d, j, Kseq (k1, i, k2) else
        if d <> None then raise Exit else
        let st, d, j, k2 = get_stack st k2 in
        st, d, j, Kseq (k1, i, k2)
    | Ktag (tag, k2) ->
        let st, d, i, k2 = get_stack st k2 in st, d, i, Ktag (tag, k2)
    | Kpar ((Kstop _) as k1, k2) ->
        let st, d, i, k2 = get_stack st k2 in st, d, i, Kpar (k1, k2)
    | Kpar _ | Kif _ | Kcase _ | Khavoc _ | Kstop _ -> raise Exit in
  let st, d, i, k = get_stack [] k in
  if i <> 0 then raise Exit else
  match d with
  | Some (t, f) ->
      let unwind t ({pv_vs = v}, d) = match d with
        | Some d -> t_let_close_simp v d t
        | None when t_v_occurs v t > 0 -> raise Exit
        | None -> t in
      let t = List.fold_left unwind t st in
      let f = if t_closed f then f else
              List.fold_left unwind f st in
      t, f, k
  | None -> raise Exit

(* stage 1: expr -> kode *)

let k_unit res = Kval ([res], t_true)

let bind_oldies o2v k = Mpv.fold (fun o v k ->
  Kseq (Klet (o, t_var v.pv_vs, t_true), 0, k)) o2v k

let k_havoc loc eff k =
  if Sreg.is_empty eff.eff_covers then k else
  let conv wr = Mpv.map (fun () -> None) wr in
  Kseq (Khavoc (Mreg.map conv eff.eff_writes, loc), 0, k)

(* missing exceptional postconditions are set to True,
   unless we skip them altogether and let the exception
   escape into the outer code (only for abstract blocks) *)
let complete_xpost cty {eff_raises = xss} skip =
  Mxs.set_union (Mxs.set_inter cty.cty_xpost xss)
    (Mxs.map (fun () -> []) (Mxs.set_diff xss skip))

let wp_solder expl wp =
  if can_simp wp then wp else
  let wp = t_attr_add stop_split wp in
  if attrs_has_expl wp.t_attrs then wp else t_attr_add expl wp

let rec explain_inv loc f = match f.t_node with
  | Tapp _ -> vc_expl loc Sattr.empty expl_type_inv f
  | _ -> t_map (explain_inv loc) (t_attr_set ?loc Sattr.empty f)

let inv_of_pvs, inv_of_loop =
  let a = create_tvsymbol (id_fresh "a") in
  let ps_dummy = create_psymbol (id_fresh "dummy") [ty_var a] in
  let mk_dummy v = ps_app ps_dummy [t_var v.pv_vs] in
  let add_varl fl (t,_) = ps_app ps_dummy [t] :: fl in
  (fun {known_map = kn} loc pvs ->
    let fl = List.map mk_dummy (Spv.elements pvs) in
    List.map (explain_inv loc) (Typeinv.inspect kn fl)),
  (fun {known_map = kn} loc fl varl ->
    let fl = List.fold_left add_varl fl varl in
    List.map (explain_inv loc) (Typeinv.inspect kn fl))

let assume_inv inv k = Kseq (Kval ([], inv), 0, k)
let assert_inv inv k = Kpar (Kstop inv, assume_inv inv k)

let inv_of_pure {known_map = kn} loc fl k =
  let add f k = assert_inv (explain_inv loc f) k in
  List.fold_right add (Typeinv.inspect kn fl) k

(* translate the expression [e] into a k-expression:
   [lps] stores the variants of outer recursive functions
   [res] names the result of the normal execution of [e]
   [xmap] maps every raised exception to a pair [i,xres]:
   - [i] is a positive int assigned at the catching site
   - [xres] names the value carried by the exception
   [case_xmap] is used for match-with-exceptions *)
let rec k_expr env lps e res xmap =
  let loc = e.e_loc and eff = e.e_effect in
  let attrs = Sattr.diff e.e_attrs vc_attrs in
  let t_tag t = t_attr_set ?loc attrs t in
  let var_or_proxy_case xmap e k =
    match e.e_node with
    | Evar v -> k v
    | _ -> let v = proxy_of_expr e in
           Kseq (k_expr env lps e v xmap, 0, k v) in
  let var_or_proxy = var_or_proxy_case xmap in
  let check_divergence k =
    if diverges eff.eff_oneway && not env.divergent then begin
      if Debug.test_noflag debug_ignore_diverges then
      Warning.emit ?loc "termination@ of@ this@ expression@ \
        cannot@ be@ proved,@ but@ there@ is@ no@ `diverges'@ \
        clause@ in@ the@ outer@ specification";
      Kpar (Kstop (vc_expl loc attrs expl_divergent t_false), k)
    end else k in
  let k = match e.e_node with
    | Evar v ->
        Klet (res, t_tag (t_var v.pv_vs), t_true)
    | Econst c ->
        Klet (res, t_tag (t_const c (ty_of_ity e.e_ity)), t_true)
    | Eexec ({c_node = Cfun e1; c_cty = {cty_args = []} as cty}, _)
      when Sattr.mem wb_attr e.e_attrs ->
        (* white-box blocks do not hide their contents from the external
           computation. Instead, their pre and post are simply added as
           assertions at the beginning and the end of the expression.
           All preconditions are thus preserved (as with kp_attr).
           White-box blocks do not force type invariants. *)
        let k_of_post expl v ql =
          let make = let t = t_var v.pv_vs in fun q ->
            vc_expl None attrs expl (open_post_with t q) in
          let sp = t_and_asym_l (List.map make ql) in
          let k = match sp.t_node with
            | Tfalse -> Kstop sp | _ -> Kcut sp in
          inv_of_pure env loc [sp] k in
        (* normal pre- and postcondition *)
        let pre = wp_of_pre None attrs cty.cty_pre in
        let pre = inv_of_pure env loc [pre] (Kcut pre) in
        let post = k_of_post expl_post res cty.cty_post in
        (* handle exceptions that pass through *)
        let xs_pass = eff.eff_raises in
        let xq_pass = Mxs.set_inter cty.cty_xpost xs_pass in
        let xq_pass = Mxs.inter (fun _ ql (i,v) ->
          let xq = k_of_post expl_xpost v ql in
          Some ((i,v), Kseq (xq, 0, Kcont i))) xq_pass xmap in
        (* each exception raised in e1 but not in e is hidden
           due to an exceptional postcondition False in xpost *)
        let bot = Kstop (vc_expl loc attrs expl_absurd t_false) in
        let xs_lost = Sxs.diff e1.e_effect.eff_raises xs_pass in
        let xq_lost = Mxs.set_inter cty.cty_xpost xs_lost in
        let xq_lost = Mxs.mapi (fun xs ql ->
          let v = res_of_post xs.xs_ity ql in
          let xq = k_of_post expl_xpost v ql in
          (new_exn env, v), Kseq (xq, 0, bot)) xq_lost in
        (* complete xmap with new indices, then handle e1 *)
        let xmap = Mxs.set_union (Mxs.map fst xq_lost) xmap in
        let k = Kseq (k_expr env lps e1 res xmap, 0, post) in
        let add_xq _ ((i,_), xq) k = Kseq (k, i, xq) in
        let k = Mxs.fold add_xq xq_lost k in
        let k = Mxs.fold add_xq xq_pass k in
        let k = bind_oldies cty.cty_oldies k in
        (* ignore divergence here if we check it later *)
        let k = if Sattr.mem nt_attr e1.e_attrs
                then check_divergence k else k in
        if cty.cty_pre = [] then k else Kseq (pre, 0, k)
    | Eexec (ce, ({cty_pre = pre; cty_oldies = oldies} as cty)) ->
        (* [ VC(ce) (if ce is a lambda executed in-place)
           | STOP pre
           | HAVOC ; [ ASSUME post | ASSUME xpost ; RAISE ] ] *)
        let p, (oldies, sbs) = match pre with
          (* for recursive calls, compute the 'variant decrease'
             precondition and rename the oldies to avoid clash *)
          | {t_node = Tapp (ls, tl)} :: pl when Mls.mem ls lps ->
              let ovl, rll = Mls.find ls lps in
              let nvl = List.combine tl rll in
              let d = decrease env loc attrs expl_variant ovl nvl in
              wp_and d (wp_of_pre loc attrs pl), renew_oldies oldies
          | pl -> wp_of_pre loc attrs pl, (oldies, Mvs.empty) in
        let trusted = match ce.c_node with
          | (Capp ({rs_logic = RLls ls}, _) | Cpur (ls, _))
            when ce.c_cty.cty_args = [] (* fully applied *) ->
              Typeinv.is_trusted_constructor env.known_map ls ||
              Typeinv.is_trusted_projection env.known_map ls e.e_ity
          | _ -> false in
        let rds = cty.cty_effect.eff_reads in
        let aff = pvs_affected cty.cty_effect.eff_covers rds in
        let pinv = if trusted then [] else inv_of_pvs env e.e_loc rds in
        let qinv = if trusted then [] else inv_of_pvs env e.e_loc aff in
        let k_of_post expl v ql =
          let sp = sp_of_post loc attrs expl v ql in
          let sp = t_subst sbs sp (* rename oldies *) in
          let rinv = if trusted then [] else
            inv_of_pvs env e.e_loc (Spv.singleton v) in
          match term_of_post ~prop:false v.pv_vs sp with
          | Some (t, sp) ->
              Klet (v, t_tag t, List.fold_right sp_and rinv sp)
          | None ->  Kval ([v], List.fold_right sp_and rinv sp) in
        let k = k_of_post expl_post res cty.cty_post in
        (* in abstract blocks, exceptions without postconditions
           escape from the block into the outer code. Otherwise,
           every exception in eff_raises is an alternative block
           with the xpost assumed and the exception raised. *)
        let skip = match ce.c_node with
          | Cfun _ -> xmap | _ -> Mxs.empty in
        let xq = complete_xpost cty eff skip in
        let k = Mxs.fold2_inter (fun _ ql (i,v) k ->
          let xk = k_of_post expl_xpost v ql in
          Kpar(k, Kseq (xk, 0, Kcont i))) xq xmap k in
        let k = List.fold_right assume_inv qinv k in
        (* oldies and havoc are common for all outcomes *)
        let k = bind_oldies oldies (k_havoc loc eff k) in
        (* ignore divergence here if we check it later *)
        let k = match ce.c_node with
          | Cfun e when not (Sattr.mem nt_attr e.e_attrs) -> k
          | _ -> check_divergence k in
        let k = if pre = [] then k else
          if Sattr.mem kp_attr e.e_attrs
            then Kseq (Kcut p, 0, k)
            else Kpar (Kstop p, k) in
        let k = List.fold_right assert_inv pinv k in
        begin match ce.c_node with
          | Cfun e -> Kpar (k_fun env lps ~xmap ce.c_cty e, k)
          | _ -> k end
    | Eassign asl ->
        let cv = eff.eff_covers in
        if Sreg.is_empty cv then k_unit res else
        (* compute the write effect *)
        let add wr (r,f,v) =
          let f = fd_of_rs f in
          let r = match r.pv_ity.ity_node with
            | Ityreg r -> r | _ -> assert false in
          Mreg.change (function
            | None   -> Some (Mpv.singleton f v)
            | Some s -> Some (Mpv.add f v s)) r wr in
        let wr = List.fold_left add Mreg.empty asl in
        (* we compute the same region bijection as in eff_assign,
           except we do not need any consistency checking now *)
        let reg_rexp {reg_its = s; reg_args = tl; reg_regs = rl} wfs =
          let ity_rexp xl t = ity_exp_fold (fun l r -> r :: l) xl t in
          let sbs = its_match_regs s tl rl in
          let mfield xl f = match Mpv.find_opt f wfs with
            | Some v -> ity_rexp xl v.pv_ity
            | None -> ity_rexp xl (ity_full_inst sbs f.pv_ity) in
          List.fold_left mfield [] s.its_mfields in
        let rec stitch t2f rf rt wfs =
          List.fold_left2 link (Mreg.add rt rf t2f)
            (reg_rexp rf Mpv.empty) (reg_rexp rt wfs)
        and link t2f rf rt =
          stitch t2f rf rt (Mreg.find_def Mpv.empty rt wr) in
        (* renaming of regions "dst-to-src" under the surviving regions *)
        let add_write r wfs t2f = stitch t2f r r wfs in
        let t2f = Mreg.fold add_write (Mreg.set_inter wr cv) Mreg.empty in
        (* rearrange the write effect according to the renaming *)
        let add_write r wfs acc =
          try Mreg.add (Mreg.find r t2f) (Mpv.map (fun v -> Some v) wfs) acc
          with Not_found -> acc in
        Kseq (Khavoc (Mreg.fold add_write wr Mreg.empty, loc), 0, k_unit res)
    | Elet (LDvar (v, e0), e1) ->
        let k = k_expr env lps e1 res xmap in
        Kseq (k_expr env lps e0 v xmap, 0, k)
    | Elet ((LDsym _| LDrec _) as ld, e1) ->
        let k = k_expr env lps e1 res xmap in
        (* when we havoc the VC of a locally defined function,
           we must take into account every write in the following
           expression and ignore the resets, because the function
           may be executed before the resets. *)
        let eff = eff_write e1.e_effect.eff_reads
                            e1.e_effect.eff_writes in
        (* postcondition, as in [Pdecl.create_let_decl] *)
        let add_axiom cty q k = if can_simp q then k else
          let p = Kval (cty.cty_args, sp_of_pre cty.cty_pre) in
          let ax = Kseq (p, 0, bind_oldies cty.cty_oldies (Kstop q)) in
          Kseq (Kaxiom (k_havoc loc eff ax), 0, k) in
        let add_axiom cty q k =
          let pinv = inv_of_pvs env loc (cty_reads cty) in
          List.fold_right assert_inv pinv (add_axiom cty q k) in
        let add_rs sm s c (vl,k) = match s.rs_logic with
          | RLls _ -> assert false (* not applicable *)
          | RLnone -> vl, k
          | RLlemma ->
              let v = res_of_cty c.c_cty and q = c.c_cty.cty_post in
              let q = sp_of_post None Sattr.empty expl_post v q in
              let q = if pv_is_unit v
                then t_subst_single v.pv_vs t_void q
                else t_exists_close_simp [v.pv_vs] [] q in
              vl, add_axiom c.c_cty q k
          | RLpv v ->
              let c = if Mrs.is_empty sm then c else c_rs_subst sm c in
              let q = cty_exec_post (cty_enrich_post c) in
              let q = sp_of_post None Sattr.empty expl_post v q in
              v::vl, add_axiom c.c_cty q k in
        let vl, k = match ld with
          | LDrec rdl ->
              let add_rd sm d = Mrs.add d.rec_rsym d.rec_sym sm in
              let sm = List.fold_left add_rd Mrs.empty rdl in
              let add_rd d dl = add_rs sm d.rec_sym d.rec_fun dl in
              List.fold_right add_rd rdl ([], k)
          | LDsym (s,c) -> add_rs Mrs.empty s c ([], k)
          | LDvar _ -> assert false (* not applicable *) in
        let k = if vl = [] then k else Kseq (Kval (vl, t_true), 0, k) in
        (* precondition *)
        begin match ld with
          | LDrec rdl ->
              let rec k_par = function
                | [k] -> k | [] -> assert false
                | k::kl -> Kpar (k, k_par kl) in
              Kpar (k_havoc loc eff (k_par (k_rec env lps rdl)), k)
          | LDsym (_, {c_node = Cfun e; c_cty = cty}) ->
              Kpar (k_havoc loc eff (k_fun env lps cty e), k)
          | _ -> k end
    | Eif (e0, e1, e2) ->
        (* with both branches pure, switch to SP to avoid splitting *)
        let s = eff_pure e1.e_effect && eff_pure e2.e_effect in
        let k1 = k_expr env lps e1 res xmap in
        let k2 = k_expr env lps e2 res xmap in
        let kk v =
          if s then try
            if not (ity_equal e.e_ity ity_bool) ||
              ity_fragile e.e_ity then raise Exit;
            let t1, f1, k1 = term_of_kode res k1 in
            let t2, f2, k2 = term_of_kode res k2 in
            let test = t_equ (t_var v.pv_vs) t_bool_true in
            (* with both branches simple, define a resulting term *)
            let t = t_if_simp test t1 t2 and f = sp_if test f1 f2 in
            Kseq (Ktag (SP, Kif (v, k1, k2)), 0, Klet (res, t, f))
          with Exit -> Ktag (SP, Kif (v, k1, k2))
          else Kif (v, k1, k2) in
        var_or_proxy e0 kk
    | Ematch (e0, bl, xl) ->
        (* try-with is just another semicolon *)
        let branch xs (vl,e) (xl,xm) =
          let i = new_exn env in
          let xk = k_expr env lps e res xmap in
          (* a single pv for the carried value *)
          let v, xk = match vl with
            | [] -> pv_of_ity "_" ity_unit, xk
            | [v] -> v, xk
            | vl ->
                let v = pv_of_ity "exv" xs.xs_ity in
                let cs = fs_tuple (List.length vl) in
                let pl = List.map (fun v -> pat_var v.pv_vs) vl in
                v, Kcase (v, [pat_app cs pl v.pv_vs.vs_ty, xk]) in
          (i,xk)::xl, Mxs.add xs (i,v) xm in
        let xl, cxmap = Mxs.fold branch xl ([], xmap) in
        (* with all branches pure, switch to SP to avoid splitting *)
        let s = List.for_all (fun (_,e) -> eff_pure e.e_effect) bl in
        let branch (pp,e) = pp.pp_pat, k_expr env lps e res xmap in
        let bl = List.map branch bl in
        let kk v =
          if s then (* try
            if ity_fragile e.e_ity then raise Exit;
            let add_br (p,k) (bl,tl,fl) =
              let t, f, k = term_of_kode res k in
              let tl = t_close_branch p t :: tl in
              (p,k)::bl, tl, t_close_branch p f :: fl in
            let bl, tl, fl = List.fold_right add_br bl ([],[],[]) in
            (* with all branches simple, define a resulting term *)
            let tv = t_var v.pv_vs in
            let t = t_case tv tl and f = sp_case tv fl in
            Kseq (Ktag (SP, Kcase (v, bl)), 0, Klet (res, t, f))
          with Exit -> *)
            Ktag (SP, Kcase (v, bl))
          else Kcase (v, bl) in
        let k = match bl with
          | [] ->
              k_expr env lps e0 res cxmap
          | [{pat_node = Pvar v}, k1] ->
              Kseq (k_expr env lps e0 (restore_pv v) cxmap, 0, k1)
          | [p, k1] when Svs.is_empty p.pat_vars ->
              Kseq (k_expr env lps e0 (proxy_of_expr e0) cxmap, 0, k1)
          | _ ->
              var_or_proxy_case cxmap e0 kk in
        (* caught xsymbols are converted to unique integers,
           so that we can now serialise the "with" clauses
           and avoid capturing the wrong exceptions *)
        List.fold_left (fun k (i,xk) -> Kseq (k,i,xk)) k xl
    | Eraise (xs, e0) ->
        let i, v = Mxs.find xs xmap in
        Kseq (k_expr env lps e0 v xmap, 0, Kcont i)
    | Eassert (Assert, f) ->
        let f = vc_expl None attrs expl_assert f in
        let k = Kseq (Kcut f, 0, k_unit res) in
        inv_of_pure env e.e_loc [f] k
    | Eassert (Assume, f) ->
        let f = vc_expl None attrs expl_assume f in
        let k = Kval ([res], f) in
        inv_of_pure env e.e_loc [f] k
    | Eassert (Check, f) ->
        let f = vc_expl None attrs expl_check f in
        let k = Kpar (Kstop f, k_unit res) in
        inv_of_pure env e.e_loc [f] k
    | Eghost e0
    | Eexn (_,e0) ->
        k_expr env lps e0 res xmap
    | Epure t ->
        let t = if t.t_ty <> None then t_tag t else
          t_if_simp (t_tag t) t_bool_true t_bool_false in
        let k = Klet (res, t, t_true) in
        inv_of_pure env e.e_loc [t] k
    | Eabsurd ->
        Kstop (vc_expl loc attrs expl_absurd t_false)
    | Ewhile (e0, invl, varl, e1) ->
        (* [ STOP inv
           | HAVOC ; ASSUME inv ; IF e0 THEN e1 ; STOP inv
                                        ELSE SKIP ] *)
        let init = wp_of_inv None attrs expl_loop_init invl in
        let prev = sp_of_inv None attrs expl_loop_init invl in
        let keep = wp_of_inv None attrs expl_loop_keep invl in
        let oldies, ovarl = oldify_variant varl in
        let decr = decrease env loc attrs expl_loop_vari ovarl varl in
        let keep = wp_and decr keep in
        let iinv = inv_of_loop env e.e_loc invl varl in
        let j = List.fold_right assert_inv iinv (Kstop init) in
        let k = List.fold_right assert_inv iinv (Kstop keep) in
        let k = Kseq (k_expr env lps e1 res xmap, 0, k) in
        let k = var_or_proxy e0 (fun v -> Kif (v, k, k_unit res)) in
        let k = Kseq (Kval ([], prev), 0, bind_oldies oldies k) in
        let k = List.fold_right assume_inv iinv k in
        let k = check_divergence k in
        Kpar (j, k_havoc loc eff k)
    | Efor (vx, (a, d, b), vi, invl, e1) ->
        let int_of_pv = match vx.pv_vs.vs_ty.ty_node with
          | Tyapp (s,_) when ts_equal s ts_int ->
              fun v -> t_var v.pv_vs
          | Tyapp (s,_) ->
              let s = int_of_range env s in
              fun v -> fs_app s [t_var v.pv_vs] ty_int
          | Tyvar _ -> assert false (* never *) in
        let a = int_of_pv a and i = t_var vi.pv_vs in
        let b = int_of_pv b and one = t_nat_const 1 in
        let init = wp_of_inv None attrs expl_loop_init invl in
        let prev = sp_of_inv None attrs expl_loop_init invl in
        let keep = wp_of_inv None attrs expl_loop_keep invl in
        let gt, le, pl = match d with
          | To     -> env.ps_int_gt, env.ps_int_le, env.fs_int_pl
          | DownTo -> env.ps_int_lt, env.ps_int_ge, env.fs_int_mn in
        let bounds = t_and (ps_app le [a; i]) (ps_app le [i; b]) in
        let expl_bounds f = vc_expl loc attrs expl_for_bound f in
        let i_pl_1 = fs_app pl [i; one] ty_int in
        let b_pl_1 = fs_app pl [b; one] ty_int in
        let init = t_subst_single vi.pv_vs a init in
        let keep = t_subst_single vi.pv_vs i_pl_1 keep in
        let last = t_subst_single vi.pv_vs b_pl_1 prev in
        let iinv = inv_of_loop env e.e_loc invl [] in
        let j = List.fold_right assert_inv iinv (Kstop init) in
        let k = List.fold_right assert_inv iinv (Kstop keep) in
        let k = Kseq (k_expr env lps e1 res xmap, 0, k) in
        let k =
          if pv_equal vx vi then
            Kseq (Kval ([vx], sp_and bounds prev), 0, k)
          else
            Kseq (Kval ([vx], t_true), 0,
            Kseq (Klet (vi, int_of_pv vx, sp_and bounds prev), 0, k))
        in
        let k = Kpar (k, Kval ([res], last)) in
        let k = List.fold_right assume_inv iinv k in
        let k = Kpar (j, k_havoc loc eff k) in
        let k = check_divergence k in
        (* [ ASSUME a <= b+1 ;
             [ STOP inv[a]
             | HAVOC ; [ ASSUME a <= v <= b /\ inv[v] ; e1 ; STOP inv[v+1]
                       | ASSUME inv[b+1] ] ]
           | ASSUME a > b+1 ] *)
        Kpar (Kseq (Kval ([], expl_bounds (ps_app le [a; b_pl_1])), 0, k),
           Kseq (Kval ([res], expl_bounds (ps_app gt [a; b_pl_1])), 0,
                 Ktag (Off expl_off_bound, Kcont 0)))
  in
  if Sattr.mem sp_attr e.e_attrs then Ktag (SP, k) else
  if Sattr.mem wp_attr e.e_attrs then Ktag (WP, k) else k

and k_fun env lps ?(oldies=Mpv.empty) ?(xmap=Mxs.empty) cty e =
  (* ASSUME pre ; LET o = arg ; TRY e ; STOP post WITH STOP xpost *)
  let res, q = wp_of_post expl_post cty.cty_result cty.cty_post in
  let xq = complete_xpost cty e.e_effect xmap in
  let xq = Mxs.mapi (fun xs ql ->
    let v, xq = wp_of_post expl_xpost xs.xs_ity ql in
    (new_exn env, v), xq) xq in
  let xmap = Mxs.set_union (Mxs.map fst xq) xmap in
  let rds = List.fold_right Spv.add cty.cty_args cty.cty_effect.eff_reads in
  let aff = pvs_affected cty.cty_effect.eff_covers rds in
  let pinv = inv_of_pvs env e.e_loc rds in
  let qinv = inv_of_pvs env e.e_loc aff in
  let add_qinv v q =
    (* any write in e can potentially produce a broken result.
       In absence of writes, the result cannot be broken, but
       we prefer to add the redundant commits and let them be
       eliminated by Typeinv.inject later. *)
    let rinv = inv_of_pvs env e.e_loc (Spv.singleton v) in
    let k = List.fold_right assert_inv rinv (Kstop q) in
    List.fold_right assert_inv qinv k in
  (* do not check termination if asked nicely *)
  let env = if Sattr.mem nt_attr e.e_attrs then
    { env with divergent = true } else env in
  let k = k_expr env lps e res xmap in
  let k = Kseq (k, 0, add_qinv res q) in
  let k = Mxs.fold (fun _ ((i,r), xq) k ->
    Kseq (k, i, add_qinv r xq)) xq k in
  (* move the postconditions under the VCgen tag *)
  let k = if Sattr.mem sp_attr e.e_attrs then Ktag (SP, k) else
          if Sattr.mem wp_attr e.e_attrs then Ktag (WP, k) else k in
  let k = bind_oldies oldies (bind_oldies cty.cty_oldies k) in
  let p = List.fold_right sp_and pinv (sp_of_pre cty.cty_pre) in
  Kseq (Kval (cty.cty_args, p), 0, k)

and k_rec env lps rdl =
  let k_rd {rec_fun = c; rec_varl = varl} =
    let e = match c.c_node with
      | Cfun e -> e | _ -> assert false in
    (* store in lps our variant at the entry point
       and the list of well-founded orderings
       for each function in the let-rec block *)
    let oldies, varl = oldify_variant varl in
    let add lps rd =
      let decr = Opt.get (ls_decr_of_rec_defn rd) in
      Mls.add decr (varl, List.map snd rd.rec_varl) lps in
    k_fun env (List.fold_left add lps rdl) ~oldies c.c_cty e in
  List.map k_rd rdl

(* stage 2: push sub-expressions up as far as we can *)

(* remove dead code, reassociate sequences to the right,
   and move exception-handling code to the raise site
   when there is only one. This reduces duplication of
   premises for SP and allows it to use let-in instead
   of quantifiers over an equality when possible. *)
let reflow vc_wp k =
  let join _ _ _ = Some false in
  let join = Mint.union join in
  (* count the exit points for every outcome, normal or
     exceptional; remove the subsequent code if none,
     tag the subsequent code for moving up if single.
     For every kode to be pushed up, remember if
     it can exit normally (open) or not (closed). *)
  let rec mark vc_tag k = match k with
    | Kseq ((Khavoc _ | Klet _ | Kval _ | Kcut _) as k1, 0, k2) ->
        let k2, out2 = mark vc_tag k2 in
        Kseq (k1, 0, k2), out2
    | Kseq (k1, i, k2) ->
        let k1, out1 = mark vc_tag k1 in
        begin match Mint.find_opt i out1 with
        | Some push ->
            let k2, out2 = mark vc_tag k2 in
            let k2 = if not push then k2 else
              Ktag (Push (not (Mint.mem 0 out2)), k2) in
            Kseq (k1, i, k2), join (Mint.remove i out1) out2
        | None -> k1, out1 (* dead code *) end
    | Kpar (k1, k2) ->
        let k1, out1 = mark vc_tag k1 in
        let k2, out2 = mark vc_tag k2 in
        Kpar (k1, k2), join out1 out2
    | Kif (v, k1, k2) ->
        let k1, out1 = mark vc_tag k1 in
        let k2, out2 = mark vc_tag k2 in
        Kif (v, k1, k2), join out1 out2
    | Kcase (v, bl) ->
        let branch (p, k1) (bl, out2) =
          let k1, out1 = mark vc_tag k1 in
          (p,k1)::bl, join out1 out2 in
        let bl, out = List.fold_right branch bl ([], Mint.empty) in
        Kcase (v, bl), out
    | Khavoc _ | Klet _ | Kval _ | Kcut _ ->
        k, Mint.singleton 0 true
    | Kstop _ ->
        k, Mint.empty
    | Kcont i ->
        k, Mint.singleton i true
    | Kaxiom k ->
        let k, _ = mark WP k in
        Kaxiom k, Mint.singleton 0 true
    | Ktag ((Off _) as tag, k) ->
        let k, out = mark vc_tag k in
        Ktag (tag, k), out
    | Ktag ((WP|SP) as tag, k) when tag <> vc_tag ->
        let k, out = mark tag k in
        (* A switch from SP to WP is only sound when the kode
           has no outcomes at all, otherwise we refuse and fail.
           Therefore, WP ((SP k1); k2) cannot be SP (k1; WP k2),
           and we forbid pushing under another VCgen altogether.
           We also store the exact outcomes of k in Out, to be
           able to filter the context when switching to SP. *)
        (* TODO: provide localisation for the error message *)
        if tag = WP && not (Mint.is_empty out) then
          Loc.errorm "Cannot switch to the classical WP procedure";
        Ktag (Out out, Ktag (tag, k)), Mint.map Util.ffalse out
    | Ktag ((WP|SP), k) ->
        mark vc_tag k
    | Ktag ((Out _|Push _), _) ->
        assert false (* cannot happen *)
  in
  let rec push k q = match k with
    | Kseq (k1, i, Ktag (Push cl, k2)) ->
        (* if k2 is open but we push a closed code
           for 0 in it, then k2 becomes closed *)
        let cl = cl || match Mint.find_opt 0 q with
          | Some (_, cl) -> cl | None -> false in
        let q = Mint.add i (push k2 q, cl) q in
        (* if k2 is an open exception-handling code
           being pushed in k1, then we must still
           raise i after k2 and catch it here *)
        if i = 0 || cl then push k1 q else
        Kseq (push k1 q, i, Kcont 0)
    | Kseq (k1, i, k2) ->
        Kseq (push k1 (Mint.remove i q), i, push k2 q)
    | Kpar (k1, k2) ->
        Kpar (push k1 q, push k2 q)
    | Kif (v, k1, k2) ->
        Kif (v, push k1 q, push k2 q)
    | Kcase (v, bl) ->
        Kcase (v, List.map (fun (p,k) -> p, push k q) bl)
    | Khavoc _ | Klet _ | Kval _ | Kcut _ ->
        begin match Mint.find_opt 0 q with
        | Some (q, _) -> Kseq (k, 0, q)
        | None -> k end
    | Kstop _ ->
        k
    | Kcont i ->
        begin match Mint.find_opt i q with
        | Some (q, cl) when i = 0 || cl -> q
        | Some (q, _) -> Kseq (q, 0, k)
        | None -> k end
    | Kaxiom k ->
        let k = push k Mint.empty in
        begin match Mint.find_opt 0 q with
        | Some (q, _) -> Kseq (Kaxiom k, 0, q)
        | None -> Kaxiom k end
    | Ktag ((Off _) as tag, k) ->
        Ktag (tag, push k q)
    | Ktag ((WP|SP|Out _) as tag, k) ->
        Ktag (tag, push k Mint.empty)
    | Ktag (Push _, _) ->
        assert false (* cannot happen *)
  in
  let k = if vc_wp then k else Ktag (SP, k) in
  push (fst (mark WP k)) Mint.empty

(** stage 3: WP *)

(* a "destination map" maps program variables (pre-effect state)
   to fresh vsymbols (post-effect state) *)

let dst_of_wp loc wr wp =
  if Mreg.is_empty wr then Mpv.empty else
  let clone_affected v _ =
    if pv_affected wr v then Some (clone_pv loc v) else None in
  Mpv.mapi_filter clone_affected (t_freepvs Spv.empty wp)

let adjustment dst = Mpv.fold (fun o n sbs ->
  Mvs.add o.pv_vs (t_var n) sbs) dst Mvs.empty

let advancement dst0 dst1 =
  let add _ v n sbs =
    if vs_equal v n then sbs else Mvs.add v (t_var n) sbs in
  Mpv.fold2_inter add dst0 dst1 Mvs.empty

(* express shared region values as "v.f1.f2.f3" when possible *)

let rec explore_paths kn aff regs t ity =
  if ity.ity_pure then regs else
  match ity.ity_node with
  | Ityvar _ -> assert false
  | Ityreg r when not (Sreg.mem r aff) -> regs
  | Ityreg ({reg_its = s; reg_args = tl; reg_regs = rl} as r) ->
      let rec height t = match t.t_node with
        (* prefer user variables to proxy variables *)
        | Tvar v when Sattr.mem proxy_attr v.vs_name.id_attrs -> 65536
        | Tvar _ -> 0 | Tapp (_,[t]) -> height t + 1
        | _ -> assert false (* shouldn't happen *) in
      let min t o = if height t < height o then t else o in
      let regs = Mreg.change (fun o -> Some (Opt.fold min t o)) r regs in
      explore_its kn aff regs t s tl rl
  | Ityapp (s,tl,rl) -> explore_its kn aff regs t s tl rl

and explore_its kn aff regs t s tl rl =
  let itd = find_its_defn kn s in
  let sum = match itd.itd_constructors with
    | _::_::_ -> true | _ -> false in
  let isb = its_match_regs s tl rl in
  let follow regs rs =
    let ity = ity_full_inst isb rs.rs_cty.cty_result in
    if sum && ity_fragile ity then regs (* danger *) else
    let ls = ls_of_rs rs and ty = Some (ty_of_ity ity) in
    explore_paths kn aff regs (t_app ls [t] ty) ity in
  List.fold_left follow regs itd.itd_fields

let name_regions kn wr dst =
  let rec reg_aff_regs s r =
    let q = reg_exp_fold reg_aff_regs Sreg.empty r in
    let affect = not (Sreg.is_empty q) || Mreg.mem r wr in
    Sreg.union s (if affect then Sreg.add r q else q) in
  let collect o _ aff = ity_exp_fold reg_aff_regs aff o.pv_ity in
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
        let fd = fd_of_rs rs in
        match Mpv.find_opt fd wfs with
        | Some None -> fl
        | Some (Some {pv_vs = v}) ->
            let nt = fs_app (ls_of_rs rs) [nt] v.vs_ty in
            let ity = ity_full_inst isb rs.rs_cty.cty_result in
            let t, fl = havoc kn wr regs (t_var v) ity fl in
            cons_t_simp nt t fl
        | None ->
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

let print_dst dst = if Debug.test_flag debug_vc then
  Format.printf "@[vars = %a@]@." (Pp.print_list Pp.space
    (fun fmt (o,n) -> Format.fprintf fmt "(%a -> %a)"
      Ity.print_pv o Pretty.print_vs n)) (Mpv.bindings dst)

let print_regs regs = if Debug.test_flag debug_vc then
  Format.printf "@[regs = %a@]@." (Pp.print_list Pp.space
    (fun fmt (r,t) -> Format.fprintf fmt "(%a -> %a)"
      Ity.print_reg r Pretty.print_term t)) (Mreg.bindings regs)

let sp_complete sp1 wr1 wr2 =
  let add v n sp = sp_and sp (t_equ (t_var n) (t_var v.pv_vs)) in
  Mpv.fold add (Mpv.set_diff wr2 wr1) sp1

let sp_combine sp1 wr1 sp2 wr2 =
  let sp1 = sp_complete sp1 wr1 wr2 in
  let sp2 = sp_complete sp2 wr2 wr1 in
  sp_or sp1 sp2, Mpv.set_union wr1 wr2

let sp_combine_map sp1 sp2 =
  Mint.union (fun _ (sp1, wr1) (sp2, wr2) ->
    Some (sp_combine sp1 wr1 sp2 wr2)) sp1 sp2

(* handle multiple locations of writes *)

let ht_written = Hvs.create 17

let fresh_loc_attrs = Loc.dummy_position, Sattr.empty

let wrt_mk_loc_attr loc =
  Opt.map (fun loc -> loc, create_written_attr loc) loc

let wrt_add_loc_attr v = function
  | Some (loc,attr) ->
      begin match Hvs.find ht_written v with
      | _, attrs ->
          let attrs = Sattr.add attr attrs in
          Hvs.replace ht_written v (loc,attrs)
      | exception Not_found -> ()
      end
  | None -> ()

let wrt_rename quant vl f =
  let rename v sbs =
    match Hvs.find ht_written v with
    | _,attrs when Sattr.is_empty attrs ->
        v, sbs (* no write sites, strange *)
    | loc,attrs ->
        let id =
          if Sattr.cardinal attrs = 1 then (* single write site *)
            id_user ~attrs:v.vs_name.id_attrs v.vs_name.id_string loc
          else (* multiple write sites *)
            id_clone ~attrs v.vs_name in
        let nv = create_vsymbol id v.vs_ty in
        nv, Mvs.add v (t_var nv) sbs
    | exception Not_found ->
        v, sbs in
  let vl, sbs = Lists.map_fold_right rename vl Mvs.empty in
  quant vl (t_subst sbs f)

let wrt_forall vl f = wrt_rename wp_forall vl f
let wrt_exists vl f = wrt_rename sp_exists vl f

(* compute compact verification conditions, in the style
   of the Flanagan and Saxe paper (POPL'01).

   Here is how it works, on a small example:

      sp_expr kn k
              rdm = [0 -> {v1; v2}; 1 -> {v1; v3}]
              dst = [v1 -> u1; v2 -> u2; v3 -> u3]
      = (wp, [0 -> (sp_0, [v1 -> u1]);
              1 -> (sp_1, [v3 -> u3])], {v0; v1})

   [sp_expr kn k rdm dst] returns a triple [(wp, sp+wr, rd)].

   The mapping [rdm] provides the post-reads set for every
   possible outcome of [k]. If [k] ends normally (outcome 0),
   the subsequent execution will read program variables [v1]
   and [v2]. If [k] terminates with an exception (outcome 1),
   the subsequent execution will read [v1] and [v3].

   The mapping [dst] provides post-write names for every
   mutable variable in [rdm]. If [k] modifies [v1] (on any
   execution path), the final value must be put in [u1],
   and similarly for [v2] and [v3].

   The set [rd] contains every previously defined or declared
   variable that may be read by [k] or by the subsequent code
   for any outcome of [k]. In our example, [k] and the code
   after [k] depends on [v0] and [v1]; the variables [v2] and
   [v3] are defined or declared by [k] itself and thus do not
   appear in [rd].

   The formula [wp] is a safety precondition of [k], logically
   equivalent to [WP(k,true)]. Every free variable in [wp] is
   in [rd].

   The mapping [sp+wr] provides the postcondition [sp_i] and
   the actual write effect [wr_i] for every outcome [i] of [k].
   The write effect [wr_i] is necessarily a submap of [dst]
   restricted to the corresponding post-read set [rdm(i)].
   For example, it is possible that [k] also modifies [v3]
   on the normal execution path, but since [v3] is not read
   after the normal termination of [k], it is not in [wr_0].
   Every free variable in [sp_i] is either in [rd] or in
   the range of [wr_i], or otherwise in [rdm(i)]. Every
   variable in the range of [wr_i] is free in [sp_i]. *)

let rec sp_expr kn k rdm dst = match k with
  | Kseq (Klet (v, t, f), 0, k2) ->
      let wp2, sp2, rd2 = sp_expr kn k2 rdm dst in
      let rd1 = t_freepvs (t_freepvs rd2 t) f in
      let wp = wp_let v t (sp_implies f wp2) in
      let close _ (sp, wr) rd =
        Some (sp_let v t (sp_and f sp) rd, wr) in
      wp, Mint.inter close sp2 rdm, Spv.remove v rd1
  | Kseq (k1, i, k2) ->
      let wp2, sp2, rd2 = sp_expr kn k2 rdm dst in
      (* log new "written" variables added to dst *)
      let new_written = ref [] in
      let mk_written v =
        let n = clone_pv None v in
        if relevant_for_counterexample v.pv_vs.vs_name then begin
          Hvs.add ht_written n fresh_loc_attrs;
          new_written := n :: !new_written
        end;
        n in
      (* the dst parameter for k1 must include a fresh final
         name for every variable modified by k2 (on any path),
         and for every variable read by k2 that is not in dst *)
      let get_wr _ (_, w) m = Mpv.set_union w m in
      let wr2 = Mint.fold get_wr sp2 Mpv.empty in
      let fresh_wr2 v _ = mk_written v in
      let fresh_rd2 v _ = if v.pv_ity.ity_pure then None
                          else Some (mk_written v) in
      let wp1, sp1, rd1 = sp_expr kn k1 (Mint.add i rd2 rdm)
        (Mpv.set_union (Mpv.set_union (Mpv.mapi fresh_wr2 wr2)
        (Mpv.mapi_filter fresh_rd2 (Mpv.set_diff rd2 dst))) dst) in
      (* retrieve the postcondition and the write effect for the
         outcome i: they prepend everything that happens in k2 *)
      let sp0, wr0 = Mint.find i sp1 in
      (* in (sp0 -> wp2) we bind everything that is not in rd1,
         knowing that variables that are not in rd2 are already
         bound in sp0. We also bind all the final names. *)
      let concat rd wr = List.rev_append (List.rev_map
        (fun v -> v.pv_vs) (Spv.elements rd)) (Mpv.values wr) in
      let bound = Spv.diff rd2 rd1 in
      let wp2 =
        (* variables in wp2 must be adjusted wrt. wr0 *)
        let adj = adjustment wr0 and vl = concat bound wr0 in
        wrt_forall vl (sp_implies sp0 (t_subst adj wp2)) in
      (* compute (sp0 /\ sp2_j) for every outcome j of k2 *)
      let close (sp, wr) rd =
        (* retrieve the write effects in wr0 that are visible
           in the post-reads of k2, i.e., are not masked by
           a write in k2 on the corresponding execution path *)
        let wr0_dst = Mpv.set_inter dst
          (Mpv.set_diff (Mpv.set_inter wr0 rd) wr) in
        let wr = Mpv.set_union wr0_dst wr in
        (* we must not bind variables that are visible in the
           post-reads of k2, so we remove the post-reads from
           bound, and we remove the visible writes from wr0 *)
        let vl = concat
          (Spv.diff bound rd) (Mpv.set_diff wr0 wr0_dst) in
        (* visible writes in sp0 are not masked by wr, and so
           must be advanced to dst. Variables in sp must then
           be adjusted wrt. this "advanced" write effect. *)
        let adj = adjustment (Mpv.set_union wr0_dst wr0) in
        let sp0 = t_subst (advancement wr0 wr0_dst) sp0 in
        wrt_exists vl (sp_and sp0 (t_subst adj sp)), wr in
      let close _ sp rd = Some (close sp rd) in
      let sp2 = Mint.inter close sp2 rdm in
      (* finally, the postcondition and the write effect for
         every other outcome of k1 must be advanced to dst *)
      let advance (sp, wr) =
        let dst = Mpv.set_inter dst wr in
        t_subst (advancement wr dst) sp, dst in
      let sp1 = Mint.map advance (Mint.remove i sp1) in
      List.iter (Hvs.remove ht_written) !new_written;
      wp_and wp1 wp2, sp_combine_map sp1 sp2, rd1
  | Kpar (k1, k2) ->
      let wp1, sp1, rd1 = sp_expr kn k1 rdm dst in
      let wp2, sp2, rd2 = sp_expr kn k2 rdm dst in
      wp_and wp1 wp2, sp_combine_map sp1 sp2, Spv.union rd1 rd2
  | Kif (v, k1, k2) ->
      let test = t_equ (t_var v.pv_vs) t_bool_true in
      let wp1, sp1, rd1 = sp_expr kn k1 rdm dst in
      let wp2, sp2, rd2 = sp_expr kn k2 rdm dst in
      let join _ sp1 sp2 = match sp1, sp2 with
        | Some (sp1, wr1), Some (sp2, wr2) ->
            let sp1 = sp_complete sp1 wr1 wr2 in
            let sp2 = sp_complete sp2 wr2 wr1 in
            Some (sp_if test sp1 sp2, Mpv.set_union wr1 wr2)
        | Some (sp1, wr1), None -> Some (sp_and test sp1, wr1)
        | None, Some (sp2, wr2) -> Some (sp_and (t_not test) sp2, wr2)
        | None, None -> None in
      let sp = Mint.merge join sp1 sp2 in
      wp_if test wp1 wp2, sp, Spv.add v (Spv.union rd1 rd2)
  | Kcase (v, bl) ->
      let t = t_var v.pv_vs in
      let branch (p, k) (wpl, spl, wrm, rds) =
        let wp, sp, rd = sp_expr kn k rdm dst in
        let wpl = t_close_branch p wp :: wpl in
        let spl = (p, sp) :: spl in
        let join _ wr1 wr2 = Some (Mpv.set_union wr1 wr2) in
        let wrm = Mint.union join (Mint.map snd sp) wrm in
        let pvs = pvs_of_vss Spv.empty p.pat_vars in
        wpl, spl, wrm, Spv.union rds (Spv.diff rd pvs) in
      let wpl, spl, wrm, rds = List.fold_right branch bl
        ([], [], Mint.empty, Spv.empty) in
      let join p _ sp spl =
        let spl, wr0 = Opt.get spl in
        let sp = match sp with
          | Some (sp, wr) -> sp_complete sp wr wr0
          | None -> t_false in
        Some (t_close_branch p sp :: spl, wr0) in
      let spm = Mint.map (fun wr -> [], wr) wrm in
      let spm = List.fold_right (fun (p,sp) spm ->
        Mint.merge (join p) sp spm) spl spm in
      let sp_case (bl, wr) = sp_case t bl, wr in
      wp_case t wpl, Mint.map sp_case spm, Spv.add v rds
  | Khavoc (wr, loc) ->
      let rd = Mint.find 0 rdm in
      let dst = Mpv.set_inter dst (pvs_affected wr rd) in
      if Mpv.is_empty dst then sp_expr kn (Kcont 0) rdm dst else
      let regs = name_regions kn wr dst in
      let () = print_dst dst; print_regs regs in
      let add _ t fvs = t_freevars fvs t in
      let fvs = Mreg.fold add regs Mvs.empty in
      let fvs = Mpv.fold (fun _ -> Mvs.remove) dst fvs in
      let loc_attr = wrt_mk_loc_attr loc in
      let update {pv_vs = o; pv_ity = ity} n sp =
        wrt_add_loc_attr n loc_attr;
        let t, fl = havoc kn wr regs (t_var o) ity [] in
        sp_and (t_and_l (cons_t_simp (t_var n) t fl)) sp in
      let sp = Mpv.fold update dst t_true in
      let sp = sp_exists (Mvs.keys fvs) sp in
      let sp = t_attr_set ?loc sp.t_attrs sp in
      let add_rhs _ rhs rd = match rhs with
        | Some v -> Spv.add v rd | None -> rd in
      let add_rhs _ = Mpv.fold add_rhs in
      let rd = Mreg.fold add_rhs wr rd in
      t_true, Mint.singleton 0 (sp, dst), rd
  | Klet (v, t, f) ->
      let rd = Mint.find 0 rdm in
      let sp = sp_let v t f rd in
      let rd = Spv.remove v (t_freepvs rd sp) in
      t_true, Mint.singleton 0 (sp, Mpv.empty), rd
  | Kval (vl, f) ->
      let rd = Mint.find 0 rdm in
      let lost v = if Spv.mem v rd then None else Some v.pv_vs in
      let sp = sp_exists (Lists.map_filter lost vl) f in
      let rd = List.fold_right Spv.remove vl (t_freepvs rd sp) in
      t_true, Mint.singleton 0 (sp, Mpv.empty), rd
  | Kcut f ->
      let rd = t_freepvs (Mint.find 0 rdm) f in
      f, Mint.singleton 0 (f, Mpv.empty), rd
  | Kstop f ->
      f, Mint.empty, t_freepvs Spv.empty f
  | Kcont i ->
      t_true, Mint.singleton i (t_true, Mpv.empty), Mint.find i rdm
  | Kaxiom k ->
      let f = wp_expr kn k Mint.empty in
      let f = vc_expl None Sattr.empty expl_lemma f in
      let rd = t_freepvs (Mint.find 0 rdm) f in
      t_true, Mint.singleton 0 (f, Mpv.empty), rd
  | Ktag (Off expl, k) ->
      let wp, sp, rd = sp_expr kn k rdm dst in
      wp_solder expl wp, sp, rd
  | Ktag (Out out, k) ->
      sp_expr kn k (Mint.set_inter rdm out) dst
  | Ktag (WP, k) ->
      assert (Mint.is_empty rdm);
      let f = wp_expr kn k Mint.empty in
      f, Mint.empty, t_freepvs Spv.empty f
  | Ktag ((Push _|SP), _) -> assert false (* cannot happen *)

and wp_expr kn k q = match k with
  | Kseq (k1, i, k2) ->
      wp_expr kn k1 (Mint.add i (wp_expr kn k2 q) q)
  | Kpar (k1, k2) ->
      wp_and (wp_expr kn k1 q) (wp_expr kn k2 q)
  | Kif ({pv_vs = v}, k1, k2) ->
      let test = t_equ (t_var v) t_bool_true in
      wp_if test (wp_expr kn k1 q) (wp_expr kn k2 q)
  | Kcase ({pv_vs = v}, bl) ->
      let branch (p,k) = t_close_branch p (wp_expr kn k q) in
      wp_case (t_var v) (List.map branch bl)
  | Khavoc (wr, loc) ->
      let q = Mint.find 0 q in
      let dst = dst_of_wp loc wr q in
      if Mpv.is_empty dst then q else
      let regs = name_regions kn wr dst in
      let () = print_dst dst; print_regs regs in
      let add _ t fvs = t_freevars fvs t in
      let fvs = Mreg.fold add regs Mvs.empty in
      let update {pv_vs = o; pv_ity = ity} n q =
        let t, fl = havoc kn wr regs (t_var o) ity [] in
        if Mvs.mem n fvs then
          sp_implies (t_and_l (cons_t_simp (t_var n) t fl)) q
        else t_let_close_simp n t (sp_implies (t_and_l fl) q) in
      let q = t_subst (adjustment dst) q in
      let q = Mpv.fold update dst q in
      wp_forall (Mvs.keys fvs) q
  | Klet (v, t, f) ->
      wp_let v t (sp_implies f (Mint.find 0 q))
  | Kval (vl, f) ->
      let q = sp_implies f (Mint.find 0 q) in
      wp_forall (List.map (fun v -> v.pv_vs) vl) q
  | Kcut f ->
      wp_and_asym f (Mint.find 0 q)
  | Kstop f ->
      f
  | Kcont i ->
      Mint.find i q
  | Kaxiom k ->
      let f = wp_expr kn k Mint.empty in
      let f = vc_expl None Sattr.empty expl_lemma f in
      sp_implies f (Mint.find 0 q)
  | Ktag (Off expl, k) ->
      wp_solder expl (wp_expr kn k q)
  | Ktag (Out out, k) ->
      wp_expr kn k (Mint.set_inter q out)
  | Ktag (SP, k) ->
      let k = Mint.fold (fun i q k -> Kseq (k, i, Kstop q)) q k in
      let wp, _, _ = sp_expr kn k Mint.empty Mpv.empty in wp
  | Ktag ((Push _|WP), _) -> assert false (* cannot happen *)

(** VCgen *)

let vc_kode {known_map = kn} vc_wp k =
  if Debug.test_flag debug_vc then
    Format.eprintf "K @[%a@]@\n" k_print k;
  let k = reflow vc_wp k in
  if Debug.test_flag debug_reflow then
    Format.eprintf "R @[%a@]@\n" k_print k;
  wp_expr kn k Mint.empty

let vc_fun env vc_wp cty e =
  vc_kode env vc_wp (k_fun env Mls.empty cty e)

let vc_rec env vc_wp rdl =
  List.map (vc_kode env vc_wp) (k_rec env Mls.empty rdl)

let mk_vc_decl kn id f =
  let {id_string = nm; id_attrs = attrs; id_loc = loc} = id in
  let attrs = if attrs_has_expl attrs then attrs else
    Sattr.add (Ident.create_attribute ("expl:VC for " ^ nm)) attrs in
  let pr = create_prsymbol (id_fresh ~attrs ?loc ("VC " ^ nm)) in
  let f = wp_forall (Mvs.keys (t_freevars Mvs.empty f)) f in
  let f = Typeinv.inject kn f in
  let f = if Debug.test_flag debug_no_eval then f else
    Eval_match.eval_match kn f in
  create_pure_decl (create_prop_decl Pgoal pr f)

let add_vc_decl kn id f vcl =
  if can_simp f then vcl else mk_vc_decl kn id f :: vcl

let vc env kn tuc d = match d.pd_node with
  | PDlet (LDvar (_, {e_node = Eexec ({c_node = Cany},_)})) ->
      []
  | PDlet (LDvar (v, e)) ->
      let env = mk_env env kn tuc in
      let c, e = match e.e_node with
        | Eexec ({c_node = Cfun e} as c, _) -> c, e
        | _ -> c_fun [] [] [] Mxs.empty Mpv.empty e, e in
      let f = vc_fun env (Debug.test_noflag debug_sp) c.c_cty e in
      add_vc_decl kn v.pv_vs.vs_name f []
  | PDlet (LDsym (s, {c_node = Cfun e; c_cty = cty})) ->
      let env = mk_env env kn tuc in
      let f = vc_fun env (Debug.test_noflag debug_sp) cty e in
      add_vc_decl kn s.rs_name f []
  | PDlet (LDrec rdl) ->
      let env = mk_env env kn tuc in
      let fl = vc_rec env (Debug.test_noflag debug_sp) rdl in
      let add rd f vcl = add_vc_decl kn rd.rec_sym.rs_name f vcl in
      List.fold_right2 add rdl fl []
  | PDtype tdl ->
      let add_witness d vcl =
        let add_fd (mv,ldl) fd e =
          let fd = fd_of_rs fd in
          let id = id_clone fd.pv_vs.vs_name in
          let ld, v = let_var id ~ghost:fd.pv_ghost e in
          Mvs.add fd.pv_vs (t_var v.pv_vs) mv, ld::ldl in
        let mv, ldl = List.fold_left2 add_fd
          (Mvs.empty, []) d.itd_fields d.itd_witness in
        let e = List.fold_right (fun f e ->
          let f = vc_expl None Sattr.empty expl_type_inv (t_subst mv f) in
          let ld, _ = let_var (id_fresh "_") (e_assert Assert f) in
          e_let ld e) d.itd_invariant e_void in
        let e = List.fold_right e_let ldl e in
        let c = c_fun [] [] [] Mxs.empty Mpv.empty e in
        let f = vc_fun (mk_env env kn tuc)
          (Debug.test_noflag debug_sp) c.c_cty e in
        add_vc_decl kn d.itd_its.its_ts.ts_name f vcl in
      let add_invariant d vcl =
        let vs_of_rs fd = (fd_of_rs fd).pv_vs in
        let vl = List.map vs_of_rs d.itd_fields in
        let expl f = vc_expl None Sattr.empty expl_type_inv f in
        let f = t_and_asym_l (List.map expl d.itd_invariant) in
        let f = t_exists_close_simp vl [] f in
        add_vc_decl kn d.itd_its.its_ts.ts_name f vcl in
      let add_itd d vcl =
        if d.itd_witness <> [] then add_witness d vcl else
        if d.itd_invariant <> [] then add_invariant d vcl else
        vcl in
      List.fold_right add_itd tdl []
  | _ -> []
