(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2016   --   INRIA - CNRS - Paris-Sud University  *)
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

let case_split = Ident.create_label "case_split"
let add_case t = t_label_add case_split t

let ls_of_rs s = match s.rs_logic with RLls ls -> ls | _ -> assert false

let clone_vs v = create_vsymbol (id_clone v.vs_name) v.vs_ty
let clone_pv v = clone_vs v.pv_vs

let pv_is_unit v = ity_equal v.pv_ity ity_unit

let pv_of_ity s ity = create_pvsymbol (id_fresh s) ity

let res_of_post ity = function
  | q::_ -> create_pvsymbol (clone_post_result q) ity
  | _ -> pv_of_ity "result" ity

let res_of_cty cty = res_of_post cty.cty_result cty.cty_post

let proxy_of_expr =
  let label = Slab.singleton proxy_label in fun e ->
  let id = id_fresh ?loc:e.e_loc ~label "o" in
  create_pvsymbol id e.e_ity

let sp_label = Ident.create_label "vc:sp"
let wp_label = Ident.create_label "vc:wp"
let lf_label = Ident.create_label "vc:liberal_for"

let vc_labels = Slab.add lf_label
  (Slab.add sp_label (Slab.add wp_label Slab.empty))

(* VCgen environment *)

type vc_env = {
  known_map : Pdecl.known_map;
  ps_int_le : lsymbol;
  ps_int_ge : lsymbol;
  ps_int_lt : lsymbol;
  ps_int_gt : lsymbol;
  fs_int_pl : lsymbol;
  fs_int_mn : lsymbol;
  exn_count : int ref;
}

let mk_env {Theory.th_export = ns} kn = {
  known_map = kn;
  ps_int_le = Theory.ns_find_ls ns ["infix <="];
  ps_int_ge = Theory.ns_find_ls ns ["infix >="];
  ps_int_lt = Theory.ns_find_ls ns ["infix <"];
  ps_int_gt = Theory.ns_find_ls ns ["infix >"];
  fs_int_pl = Theory.ns_find_ls ns ["infix +"];
  fs_int_mn = Theory.ns_find_ls ns ["infix -"];
  exn_count = ref 0;
}

let new_exn env = incr env.exn_count; !(env.exn_count)

(* FIXME: cannot verify int.why because of a cyclic dependency.
   int.Int is used for the "for" loops and for integer variants.
   We should be able to extract the necessary lsymbols from kn. *)
let mk_env env kn = mk_env (Env.read_theory env ["int"] "Int") kn

(* explanation labels *)

let expl_pre       = Ident.create_label "expl:precondition"
let expl_post      = Ident.create_label "expl:postcondition"
let expl_xpost     = Ident.create_label "expl:exceptional postcondition"
let expl_assume    = Ident.create_label "expl:assumption"
let expl_assert    = Ident.create_label "expl:assertion"
let expl_check     = Ident.create_label "expl:check"
let expl_absurd    = Ident.create_label "expl:unreachable point"
let expl_for_bound = Ident.create_label "expl:loop bounds"
let expl_loop_init = Ident.create_label "expl:loop invariant init"
let expl_loop_keep = Ident.create_label "expl:loop invariant preservation"
let expl_loop_vari = Ident.create_label "expl:loop variant decrease"
let expl_variant   = Ident.create_label "expl:variant decrease"
let _expl_type_inv  = Ident.create_label "expl:type invariant"

let lab_has_expl lab =
  Slab.exists (fun l -> Strings.has_prefix "expl:" l.lab_string) lab

let vc_expl loc lab expl f =
  let lab = Slab.add stop_split (Slab.union lab f.t_label) in
  let lab = if lab_has_expl lab then lab else Slab.add expl lab in
  t_label ?loc:(if loc = None then f.t_loc else loc) lab f

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

let sp_if c sp1 sp2 = match c.t_node, sp1.t_node, sp2.t_node with
  | Ttrue, _, _  -> sp1
  | Tfalse, _, _ -> sp2
  | Tnot _, Ttrue, Tfalse -> c
  | Tnot c, Ttrue, _ -> sp_implies c sp2
  | Tnot c, Tfalse, _ -> sp_and c sp2
  | _, Ttrue, _ -> sp_or c sp2
  | _, Tfalse, _ -> sp_and (t_not c) sp2
  | _, _, Ttrue -> sp_implies c sp1
  | _, _, Tfalse -> sp_and c sp1
  | _, _, _ -> add_case (t_if c sp1 sp2)

let sp_case t bl =
  let isfalse b = match t_open_branch b with
    | _, { t_node = Tfalse } -> true | _ -> false in
  if List.for_all isfalse bl then t_false else add_case (t_case t bl)

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

let decrease env loc lab expl olds news =
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
  vc_expl loc lab expl (decr olds news)

let old_of_pv {pv_vs = v; pv_ity = ity} =
  create_pvsymbol (id_clone v.vs_name) (ity_purify ity)

let oldify_variant varl =
  let fpv = Mpv.mapi_filter (fun v _ -> (* oldify mutable vars *)
    if ity_immutable v.pv_ity then None else Some (old_of_pv v))
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

(* convert user specifications into wp and sp *)

let wp_of_inv loc lab expl pl =
  t_and_l (List.map (vc_expl loc lab expl) pl)

let wp_of_pre loc lab pl = wp_of_inv loc lab expl_pre pl

let wp_of_post expl ity ql =
  let v = res_of_post ity ql in let t = t_var v.pv_vs in
  let make q = vc_expl None Slab.empty expl (open_post_with t q) in
  v, t_and_l (List.map make ql)

let push_stop loc lab expl f =
  let rec push f = match f.t_node with
    | Tbinop (Tand,g,h) when not (Slab.mem stop_split f.t_label) ->
        t_label_copy f (t_and (push g) (push h))
    | _ -> vc_expl loc lab expl f in
  push f

let sp_of_inv loc lab expl pl =
  t_and_l (List.map (push_stop loc lab expl) pl)

let sp_of_pre pl = sp_of_inv None Slab.empty expl_pre pl

let sp_of_post loc lab expl v ql = let t = t_var v.pv_vs in
  let push q = push_stop loc lab expl (open_post_with t q) in
  t_and_l (List.map push ql)

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

(* simplified syntax tree *)

type ktag = WP | SP | Push of bool

type kode =
  | Kseq   of kode * int * kode
  | Kpar   of kode * kode
  | Kif    of pvsymbol * kode * kode
  | Kcase  of pvsymbol * (pattern * kode) list
  | Khavoc of pvsymbol option Mpv.t Mreg.t
  | Klet   of pvsymbol * term * term
  | Kval   of pvsymbol list * term
  | Kcut   of term
  | Kstop  of term
  | Kcont  of int
  | Kaxiom of kode
  | Ktag   of ktag * kode

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
  | Khavoc _wr -> Format.fprintf fmt "HAVOC" (* TODO *)
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
  | Kcont 0 -> Format.fprintf fmt
      "SKIP"
  | Kcont i -> Format.fprintf fmt
      "RAISE %d" i
  | Kaxiom k -> Format.fprintf fmt
      "@[<hov 4>AXIOM %a@]" k_print k
  | Ktag (tag, k) ->
      let s = match tag with
        | WP -> "WP" | SP -> "SP"
        | Push true -> "PUSH CLOSED"
        | Push false -> "PUSH OPEN" in
      Format.fprintf fmt "@[<hov 4>%s %a@]" s k_print k

(** stage 1: expr -> kode *)

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

let k_unit res = Kval ([res], t_true)

let bind_oldies o2v k = Mpv.fold (fun o v k ->
  Kseq (Klet (o, t_var v.pv_vs, t_true), 0, k)) o2v k

let k_havoc eff k =
  if Sreg.is_empty eff.eff_covers then k else
  let conv wr = Mpv.map (fun () -> None) wr in
  Kseq (Khavoc (Mreg.map conv eff.eff_writes), 0, k)

let complete_xpost cty {eff_raises = xss} skip =
  Mexn.set_union (Mexn.set_inter cty.cty_xpost xss)
    (Mexn.map (fun () -> []) (Mexn.set_diff xss skip))

let rec k_expr env lps ({e_loc = loc} as e) res xmap =
  let lab = Slab.diff e.e_label vc_labels in
  let t_lab t = t_label ?loc lab t in
  let var_or_proxy e k = match e.e_node with
    | Evar v -> k v
    | _ -> let v = proxy_of_expr e in
        Kseq (k_expr env lps e v xmap, 0, k v) in
  let k = match e.e_node with
    | Evar v ->
        Klet (res, t_lab (t_var v.pv_vs), t_true)
    | Econst c ->
        Klet (res, t_lab (t_const c), t_true)
    | Eexec (c, ({cty_pre = pre; cty_oldies = oldies} as cty)) ->
        let p, (oldies, sbs) = match pre with
          | {t_node = Tapp (ls, tl)} :: pl when Mls.mem ls lps ->
              let ovl, rll = Mls.find ls lps in
              let nvl = List.combine tl rll in
              let d = decrease env loc lab expl_variant ovl nvl in
              wp_and d (wp_of_pre loc lab pl), renew_oldies oldies
          | pl -> wp_of_pre loc lab pl, (oldies, Mvs.empty) in
        let k_of_post expl v ql =
          let sp = sp_of_post loc lab expl v ql in
          let sp = t_subst sbs sp (* rename oldies *) in
          match term_of_post ~prop:false v.pv_vs sp with
          | Some (t, sp) -> Klet (v, t_lab t, sp)
          | None -> Kval ([v], sp) in
        let k = k_of_post expl_post res cty.cty_post in
        let skip = match c.c_node with
          | Cfun _ -> xmap | _ -> Mexn.empty in
        let xq = complete_xpost cty e.e_effect skip in
        let k = Mexn.fold2_inter (fun _ ql (i,v) k ->
          let xk = k_of_post expl_xpost v ql in
          Kpar(k, Kseq (xk, 0, Kcont i))) xq xmap k in
        let k = bind_oldies oldies (k_havoc e.e_effect k) in
        let k = if pre = [] then k else Kpar (Kstop p, k) in
        begin match c.c_node with
          | Cfun e -> Kpar (k_fun env lps ~xmap c.c_cty e, k)
          | _ -> k end
    | Eassign asl ->
        let cv = e.e_effect.eff_covers in
        if Sreg.is_empty cv then k_unit res else
        (* compute the write effect *)
        let add wr (r,f,v) =
          let f = Opt.get f.rs_field in
          let r = match r.pv_ity.ity_node with
            | Ityreg r -> r | _ -> assert false in
          Mreg.change (function
            | None   -> Some (Mpv.singleton f v)
            | Some s -> Some (Mpv.add f v s)) r wr in
        let wr = List.fold_left add Mreg.empty asl in
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
        Kseq (Khavoc (Mreg.fold add_write wr Mreg.empty), 0, k_unit res)
    | Elet (LDvar (v, e0), e1) ->
        let k = k_expr env lps e1 res xmap in
        Kseq (k_expr env lps e0 v xmap, 0, k)
    | Ecase (e0, [{pp_pat = {pat_node = Pvar v}}, e1]) ->
        let k = k_expr env lps e1 res xmap in
        Kseq (k_expr env lps e0 (restore_pv v) xmap, 0, k)
    | Ecase (e0, [pp, e1]) when Svs.is_empty pp.pp_pat.pat_vars ->
        let k = k_expr env lps e1 res xmap in
        Kseq (k_expr env lps e0 (proxy_of_expr e0) xmap, 0, k)
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
          Kseq (Kaxiom (k_havoc eff ax), 0, k) in
        let add_rs sm s c (vl,k) = match s.rs_logic with
          | RLls _ -> assert false (* not applicable *)
          | RLnone -> vl, k
          | RLlemma ->
              let v = res_of_cty c.c_cty and q = c.c_cty.cty_post in
              let q = sp_of_post None Slab.empty expl_post v q in
              let q = if pv_is_unit v
                then t_subst_single v.pv_vs t_void q
                else t_exists_close_simp [v.pv_vs] [] q in
              vl, add_axiom c.c_cty q k
          | RLpv v ->
              let c = if Mrs.is_empty sm then c else c_rs_subst sm c in
              let q = cty_exec_post (cty_enrich_post c) in
              let q = sp_of_post None Slab.empty expl_post v q in
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
              Kpar (k_havoc eff (k_par (k_rec env lps rdl)), k)
          | LDsym (_, {c_node = Cfun e; c_cty = cty}) ->
              Kpar (k_havoc eff (k_fun env lps cty e), k)
          | _ -> k end
    | Eif (e0, e1, e2) ->
        let s = eff_pure e1.e_effect && eff_pure e2.e_effect in
        let k1 = k_expr env lps e1 res xmap in
        let k2 = k_expr env lps e2 res xmap in
        if s then try
          let t1, f1, k1 = term_of_kode res k1 in
          let t2, f2, k2 = term_of_kode res k2 in
          var_or_proxy e0 (fun v ->
            let test = t_equ (t_var v.pv_vs) t_bool_true in
            let t = t_if_simp test t1 t2 and f = sp_if test f1 f2 in
            Kseq (Ktag (SP, Kif (v, k1, k2)), 0, Klet (res, t, f)))
        with Exit ->
          var_or_proxy e0 (fun v -> Ktag (SP, Kif (v, k1, k2)))
        else var_or_proxy e0 (fun v -> Kif (v, k1, k2))
    | Ecase (e0, bl) ->
        let s = List.for_all (fun (_,e) -> eff_pure e.e_effect) bl in
        let branch (pp,e) = pp.pp_pat, k_expr env lps e res xmap in
        let bl = List.map branch bl in
        if s then try
          let add_br (p,k) (bl,tl,fl) =
            let t, f, k = term_of_kode res k in
            let tl = t_close_branch p t :: tl in
            (p,k)::bl, tl, t_close_branch p f :: fl in
          let bl, tl, fl = List.fold_right add_br bl ([],[],[]) in
          var_or_proxy e0 (fun v -> let tv = t_var v.pv_vs in
            let t = t_case tv tl and f = sp_case tv fl in
            Kseq (Ktag (SP, Kcase (v, bl)), 0, Klet (res, t, f)))
        with Exit ->
          var_or_proxy e0 (fun v -> Ktag (SP, Kcase (v, bl)))
        else var_or_proxy e0 (fun v -> Kcase (v, bl))
    | Etry (e0, bl) ->
        let branch xs (vl,e) (xl,xm) =
          let i = new_exn env in
          let xk = k_expr env lps e res xmap in
          let v, xk = match vl with
            | [] -> pv_of_ity "_" ity_unit, xk
            | [v] -> v, xk
            | vl ->
                let v = pv_of_ity "exv" xs.xs_ity in
                let cs = fs_tuple (List.length vl) in
                let pl = List.map (fun v -> pat_var v.pv_vs) vl in
                v, Kcase (v, [pat_app cs pl v.pv_vs.vs_ty, xk]) in
          (i,xk)::xl, Mexn.add xs (i,v) xm in
        let xl, xmap = Mexn.fold branch bl ([], xmap) in
        let k = k_expr env lps e0 res xmap in
        List.fold_left (fun k (i,xk) -> Kseq (k,i,xk)) k xl
    | Eraise (xs, e0) ->
        let i, v = Mexn.find xs xmap in
        Kseq (k_expr env lps e0 v xmap, 0, Kcont i)
    | Eassert (Assert, f) ->
        let f = vc_expl None lab expl_assert f in
        Kseq (Kcut f, 0, k_unit res)
    | Eassert (Assume, f) ->
        let f = vc_expl None lab expl_assume f in
        Kval ([res], f)
    | Eassert (Check, f) ->
        let f = vc_expl None lab expl_check f in
        Kpar (Kstop f, k_unit res)
    | Eghost e0 ->
        k_expr env lps e0 res xmap
    | Epure t ->
        let t = if t.t_ty <> None then t_lab t else
          t_if_simp (t_lab t) t_bool_true t_bool_false in
        Klet (res, t, t_true)
    | Eabsurd ->
        Kstop (vc_expl loc lab expl_absurd t_false)
    | Ewhile (e0, invl, varl, e1) ->
        let init = wp_of_inv None lab expl_loop_init invl in
        let prev = sp_of_inv None lab expl_loop_init invl in
        let keep = wp_of_inv None lab expl_loop_keep invl in
        let keep, oldies =
          if varl = [] then keep, Mpv.empty else
          let oldies, ovarl = oldify_variant varl in
          let d = decrease env loc lab expl_loop_vari ovarl varl in
          wp_and d keep, oldies in
        let k = Kseq (k_expr env lps e1 res xmap, 0, Kstop keep) in
        let k = var_or_proxy e0 (fun v -> Kif (v, k, k_unit res)) in
        let k = Kseq (Kval ([], prev), 0, bind_oldies oldies k) in
        Kpar (Kstop init, k_havoc e.e_effect k)
    | Efor (v, ({pv_vs = a}, d, {pv_vs = b}), invl, e1) ->
        let a = t_var a and b = t_var b in
        let i = t_var v.pv_vs and one = t_nat_const 1 in
        let init = wp_of_inv None lab expl_loop_init invl in
        let prev = sp_of_inv None lab expl_loop_init invl in
        let keep = wp_of_inv None lab expl_loop_keep invl in
        let gt, le, pl = match d with
          | To     -> env.ps_int_gt, env.ps_int_le, env.fs_int_pl
          | DownTo -> env.ps_int_lt, env.ps_int_ge, env.fs_int_mn in
        let bounds = t_and (ps_app le [a; i]) (ps_app le [i; b]) in
        let expl_bounds f = vc_expl loc lab expl_for_bound f in
        let i_pl_1 = fs_app pl [i; one] ty_int in
        let b_pl_1 = fs_app pl [b; one] ty_int in
        let init = t_subst_single v.pv_vs a init in
        let keep = t_subst_single v.pv_vs i_pl_1 keep in
        let last = t_subst_single v.pv_vs b_pl_1 prev in
        let k = Kseq (k_expr env lps e1 res xmap, 0, Kstop keep) in
        let k = Kseq (Kval ([v], sp_and bounds prev), 0, k) in
        let k = Kpar (k, Kval ([res], last)) in
        let k = Kpar (Kstop init, k_havoc e.e_effect k) in
        if Slab.mem lf_label e.e_label then
          Kpar (Kseq (Kval ([], expl_bounds (ps_app le [a; b])), 0, k),
                   Kval ([res], expl_bounds (ps_app gt [a; b])))
        else
          Kpar (Kstop (expl_bounds (ps_app le [a; b_pl_1])), k)
  in
  if Slab.mem sp_label e.e_label then Ktag (SP, k) else
  if Slab.mem wp_label e.e_label then Ktag (WP, k) else k

and k_fun env lps ?(oldies=Mpv.empty) ?(xmap=Mexn.empty) cty e =
  let res, q = wp_of_post expl_post cty.cty_result cty.cty_post in
  let xq = complete_xpost cty e.e_effect xmap in
  let xq = Mexn.mapi (fun xs ql ->
    let v, xq = wp_of_post expl_xpost xs.xs_ity ql in
    (new_exn env, v), xq) xq in
  let xmap = Mexn.set_union (Mexn.map fst xq) xmap in
  let k = Kseq (k_expr env lps e res xmap, 0, Kstop q) in
  let k = Mexn.fold (fun _ ((i,_), xq) k ->
    Kseq (k, i, Kstop xq)) xq k in
  (* move the postconditions under the VCgen tag *)
  let k = if Slab.mem sp_label e.e_label then Ktag (SP, k) else
          if Slab.mem wp_label e.e_label then Ktag (WP, k) else k in
  let k = bind_oldies oldies (bind_oldies cty.cty_oldies k) in
  Kseq (Kval (cty.cty_args, sp_of_pre cty.cty_pre), 0, k)

and k_rec env lps rdl =
  let k_rd {rec_fun = c; rec_varl = varl} =
    let e = match c.c_node with
      | Cfun e -> e | _ -> assert false in
    if varl = [] then k_fun env lps c.c_cty e else
    let oldies, varl = oldify_variant varl in
    let add lps rd =
      let decr = Opt.get (ls_decr_of_rec_defn rd) in
      Mls.add decr (varl, List.map snd rd.rec_varl) lps in
    k_fun env (List.fold_left add lps rdl) ~oldies c.c_cty e in
  List.map k_rd rdl

(** stage 2: push sub-expressions up as far as we can *)

let reflow vc_wp k =
  let join _ _ _ = Some false in
  let join = Mint.union join in
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
        let k, _ = mark vc_tag k in
        k, Mint.singleton 0 true
    | Ktag ((WP|SP) as tag, k) when tag <> vc_tag ->
        let k, out = mark tag k in
        Ktag (tag, k), Mint.map (fun _ -> false) out
    | Ktag ((WP|SP), k) ->
        mark vc_tag k
    | Ktag (Push _, _) ->
        assert false (* cannot happen *)
  in
  let rec push k q = match k with
    | Kseq (k1, i, Ktag (Push cl, k2)) ->
        let cl = cl || match Mint.find_opt 0 q with
          | Some (_, cl) -> cl | None -> false in
        let q = Mint.add i (push k2 q, cl) q in
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
    | Ktag ((WP|SP) as tag, k) ->
        assert (Mint.is_empty q);
        Ktag (tag, push k q)
    | Ktag (Push _, _) ->
        assert false (* cannot happen *)
  in
  let k = if vc_wp then k else Ktag (SP, k) in
  push (fst (mark WP k)) Mint.empty

(** stage 3: WP *)

(* a "destination map" maps program variables (pre-effect state)
   to fresh vsymbols (post-effect state) *)

let ity_affected wr ity =
  Util.any ity_rch_fold (Mreg.contains wr) ity

let pv_affected wr v = ity_affected wr v.pv_ity

let pvs_affected wr pvs =
  if Mreg.is_empty wr then Spv.empty
  else Spv.filter (pv_affected wr) pvs

let dst_of_wp wr wp =
  if Mreg.is_empty wr then Mpv.empty else
  let clone_affected v _ =
    if pv_affected wr v then Some (clone_pv v) else None in
  Mpv.mapi_filter clone_affected (t_freepvs Spv.empty wp)

let adjustment dst = Mpv.fold (fun o n sbs ->
  Mvs.add o.pv_vs (t_var n) sbs) dst Mvs.empty

let advancement dst0 dst1 =
  let add _ v n sbs =
    if vs_equal v n then sbs else Mvs.add v (t_var n) sbs in
  Mpv.fold2_inter add dst0 dst1 Mvs.empty

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

let sensitive itd {pv_vs = f} =
  not itd.itd_its.its_private &&
  List.exists (fun i -> t_v_occurs f i > 0) itd.itd_invariant

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
        let fd = Opt.get rs.rs_field in
        match Mpv.find_opt fd wfs with
        | Some None -> fl
        | Some (Some {pv_vs = v}) ->
            if sensitive itd fd then begin
              Warning.emit "invariant-breaking updates are not yet supported";
              fl (* TODO: strong invariants *)
            end else
            let nt = fs_app (ls_of_rs rs) [nt] v.vs_ty in
            let ity = ity_full_inst isb rs.rs_cty.cty_result in
            let t, fl = havoc kn wr regs (t_var v) ity fl in
            cons_t_simp nt t fl
        | None ->
            let ity = ity_full_inst isb rs.rs_cty.cty_result in
            if ity_affected wr ity && sensitive itd fd then begin
              Warning.emit "invariant-breaking updates are not yet supported";
              fl (* TODO: strong invariants *)
            end else
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

let rec sp_expr kn k rdm dst = match k with
  | Kseq (Klet (v, t, f), 0, k2) ->
      let wp2, sp2, rd2 = sp_expr kn k2 rdm dst in
      let rd2 = t_freepvs (t_freepvs rd2 t) f in
      let wp = wp_let v t (sp_implies f wp2) in
      let close _ (sp2, wr2) rd2 =
        Some (sp_let v t (sp_and f sp2) rd2, wr2) in
      wp, Mint.inter close sp2 rdm, Spv.remove v rd2
  | Kseq (k1, i, k2) ->
      let wp2, sp2, rd2 = sp_expr kn k2 rdm dst in
      let get_wr _ (_, w) m = Mpv.set_union w m in
      let wr2 = Mint.fold get_wr sp2 Mpv.empty in
      let fresh_wr2 v _ = clone_pv v in
      let fresh_rd2 v _ = if ity_immutable v.pv_ity
                          then None else Some (clone_pv v) in
      let wp1, sp1, rd1 = sp_expr kn k1 (Mint.add i rd2 rdm)
        (Mpv.set_union (Mpv.set_union (Mpv.mapi fresh_wr2 wr2)
        (Mpv.mapi_filter fresh_rd2 (Mpv.set_diff rd2 dst))) dst) in
      let sp0, wr0 = Mint.find i sp1 in
      let bound = Spv.diff rd2 rd1 in
      let concat rd wr = List.rev_append (List.rev_map
        (fun v -> v.pv_vs) (Spv.elements rd)) (Mpv.values wr) in
      let wp2 =
        let adj = adjustment wr0 and vl = concat bound wr0 in
        wp_forall vl (sp_implies sp0 (t_subst adj wp2)) in
      let close (sp, wr) rd =
        let wr0_dst = Mpv.set_inter dst
          (Mpv.set_diff (Mpv.set_inter wr0 rd) wr) in
        let wr = Mpv.set_union wr wr0_dst in
        let vl = concat
          (Spv.diff bound rd) (Mpv.set_diff wr0 wr0_dst) in
        let adj = adjustment (Mpv.set_union wr0_dst wr0) in
        let sp0 = t_subst (advancement wr0 wr0_dst) sp0 in
        sp_exists vl (sp_and sp0 (t_subst adj sp)), wr in
      let close _ sp rd = Some (close sp rd) in
      let sp2 = Mint.inter close sp2 rdm in
      let advance (sp, wr) =
        let dst = Mpv.set_inter dst wr in
        t_subst (advancement wr dst) sp, dst in
      let sp1 = Mint.map advance (Mint.remove i sp1) in
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
  | Khavoc wr ->
      let rd = Mint.find 0 rdm in
      let dst = Mpv.set_inter dst (pvs_affected wr rd) in
      if Mpv.is_empty dst then sp_expr kn (Kcont 0) rdm dst else
      let regs = name_regions kn wr dst in
      let () = print_dst dst; print_regs regs in
      let add _ t fvs = t_freevars fvs t in
      let fvs = Mreg.fold add regs Mvs.empty in
      let fvs = Mpv.fold (fun _ -> Mvs.remove) dst fvs in
      let update {pv_vs = o; pv_ity = ity} n sp =
        let t, fl = havoc kn wr regs (t_var o) ity [] in
        sp_and (t_and_l (cons_t_simp (t_var n) t fl)) sp in
      let sp = Mpv.fold update dst t_true in
      let sp = sp_exists (Mvs.keys fvs) sp in
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
      let rd = t_freepvs (Mint.find 0 rdm) f in
      t_true, Mint.singleton 0 (f, Mpv.empty), rd
  | Ktag (WP, k) ->
      let f = wp_expr kn k (Mint.map (fun _ -> t_true) rdm) in
      let rd = t_freepvs (Mint.find_def Spv.empty 0 rdm) f in
      f, Mint.singleton 0 (t_true, Mpv.empty), rd
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
  | Khavoc wr ->
      let q = Mint.find 0 q in
      let dst = dst_of_wp wr q in
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
      sp_implies (wp_expr kn k Mint.empty) (Mint.find 0 q)
  | Ktag (SP, k) ->
      let k = Mint.fold (fun i q k -> Kseq (k, i, Kstop q)) q k in
      let wp, _, _ = sp_expr kn k Mint.empty Mpv.empty in wp
  | Ktag ((Push _|WP), _) -> assert false (* cannot happen *)

(** VCgen *)

let vc_kode {known_map = kn} vc_wp k =
  let k = reflow vc_wp k in
  if Debug.test_flag debug then
    Format.eprintf "K @[%a@]@\n" k_print k;
  wp_expr kn k Mint.empty

let vc_fun env vc_wp cty e =
  vc_kode env vc_wp (k_fun env Mls.empty cty e)

let vc_rec env vc_wp rdl =
  List.map (vc_kode env vc_wp) (k_rec env Mls.empty rdl)

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
