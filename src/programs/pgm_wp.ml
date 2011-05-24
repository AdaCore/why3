(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                     *)
(*    Jean-Christophe Filliâtre                                          *)
(*    Claude Marché                                                      *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Format
open Why
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Eval_match
open Pretty
open Pgm_ttree
open Pgm_types
open Pgm_types.T
open Pgm_module

let debug = Debug.register_flag "program_wp"

(* mutable fields *)

let mutable_fields = Hts.create 17 (* ts -> region:int -> field:int *)

let declare_mutable_field ts i j =
  let h =
    try
      Hts.find mutable_fields ts
    with Not_found ->
      let h = Hashtbl.create 17 in Hts.add mutable_fields ts h; h
  in
  Hashtbl.add h i j

(* phase 4: weakest preconditions *******************************************)

(* smart constructors for building WPs
   TODO: use simp forms / tag with label "WP" *)

let wp_and ?(sym=false) f1 f2 =
(*   if sym then t_and_simp f1 f2 else t_and_simp f1 (t_implies_simp f1 f2)  *)
  let f = t_and_simp f1 f2 in
(* experiment, but does not work
  let f = t_label_add Split_goal.stop_split f in
*)
  match f.t_node with
    | Tbinop (Tand, _, _) when not sym -> t_label_add Split_goal.asym_split f
    | _ -> f

let wp_ands ?(sym=false) fl =
  List.fold_left (wp_and ~sym) t_true fl

let wp_implies f1 f2 = match f2.t_node with
  | Tfalse -> t_implies f1 f2
  | _ -> t_implies_simp f1 f2

let find_ts ~pure uc s =
  ns_find_ts (get_namespace (if pure then pure_uc uc else impure_uc uc)) [s]
let find_ls ~pure uc s =
  ns_find_ls (get_namespace (if pure then pure_uc uc else impure_uc uc)) [s]

let is_arrow_ty ty = match ty.ty_node with
  | Tyapp (ts, _) -> ts_equal ts ts_arrow
  | _ -> false

let rec wp_forall env v f =
  let kn = get_known (pure_uc env) in
  let ty = v.vs_ty in
  let cl = match ty.ty_node with
    | Tyapp (ts, _) -> find_constructors kn ts
    | _ -> []
  in
  match cl with
    | [ls] ->
        let s = ty_match Mtv.empty (of_option ls.ls_value) ty in
        let mk_v ty = create_vsymbol (id_fresh "x") (ty_inst s ty) in
        let vl = List.map mk_v ls.ls_args in
        let t = fs_app ls (List.map t_var vl) ty in
        List.fold_right (wp_forall env) vl (t_let_close_simp v t f)
    | _ ->
        t_forall_close_simp [v] [] f

let wp_forall env v f =
  if is_arrow_ty v.vs_ty then f else
  (* if t_occurs_single v f then t_forall_close_simp [v] [] f else f *)
  match f.t_node with
    | Tbinop (Timplies, {t_node = Tapp (s,[{t_node = Tvar u};r])},h)
      when ls_equal s ps_equ && vs_equal u v && not (t_occurs_single v r) ->
        t_let_close_simp v r h
    | Tbinop (Timplies, {t_node = Tbinop (Tand, g,
                        {t_node = Tapp (s,[{t_node = Tvar u};r])})},h)
      when ls_equal s ps_equ && vs_equal u v && not (t_occurs_single v r) ->
        t_let_close_simp v r (t_implies_simp g h)
    | _ when t_occurs_single v f ->
        wp_forall env v f
    | _ ->
        f

(* utility functions for building WPs *)

let fresh_label env =
  let ty = ty_app (find_ts ~pure:true env "label_") [] in
  create_vsymbol (id_fresh "label") ty

let wp_binder env x f = match x.pv_tv with
  | Tpure _ -> wp_forall env x.pv_pure f
  | Tarrow _ -> f

let wp_binders env = List.fold_right (wp_binder env)

let add_binder x rm =
  let add r rm =
    let spv =
      try Spv.add x (Mreg.find r rm) with Not_found -> Spv.singleton x
    in
    Mreg.add r spv rm
  in
  Sreg.fold add x.pv_regions rm

let add_binders = List.fold_right add_binder

(* replace old(t) with at(t,lab) everywhere in formula f *)
let rec old_label env lab f =
  TermTF.t_map (old_label_term env lab) (old_label env lab) f

and old_label_term env lab t = match t.t_node with
  | Tapp (ls, [t]) when ls_equal ls (find_ls ~pure:true env "old") ->
      let t = old_label_term env lab t in (* NECESSARY? *)
      t_app (find_ls ~pure:true env "at") [t; t_var lab] t.t_ty
  | _ ->
      TermTF.t_map (old_label_term env lab) (old_label env lab) t

(* replace at(t,lab) with t everywhere in formula f *)
let rec erase_label env lab f =
  TermTF.t_map (erase_label_term env lab) (erase_label env lab) f

and erase_label_term env lab t = match t.t_node with
  | Tapp (ls, [t; {t_node = Tvar l}])
    when ls_equal ls (find_ls ~pure:true env "at") && vs_equal l lab ->
      erase_label_term env lab t
  | _ ->
      TermTF.t_map (erase_label_term env lab) (erase_label env lab) t

let rec unref env s f =
  TermTF.t_map (unref_term env s) (unref env s) f

and unref_term env s t = match t.t_node with
(***
  | R.Rglobal {p_ls=ls1}, Tapp (ls2, _) when ls_equal ls1 ls2 ->
      t_var v
  | R.Rlocal {pv_vs=vs1}, Tvar vs2 when vs_equal vs1 vs2 ->
      t_var v
***)
  | Tvar vs ->
      begin try t_var (Mvs.find vs s) with Not_found -> t end
  | Tapp (ls, _) when ls_equal ls (find_ls ~pure:true env "old") ->
      assert false
  | Tapp (ls, _) when ls_equal ls (find_ls ~pure:true env "at") ->
      (* do not recurse in at(...) *)
      t
  | _ ->
      TermTF.t_map (unref_term env s) (unref env s) t

let find_constructor env ts =
  let km = get_known (pure_uc env) in
  match find_constructors km ts with
  | [ls] -> ls
  | _ -> assert false

let wp_close kn rm ef f =
  let sreg = ef.E.writes in
  let sreg =
    Spv.fold (fun pv s -> Sreg.union pv.pv_regions s)
      ef.E.globals (Sreg.union ef.E.reads sreg)
  in
  (* all program variables involving these regions *)
  let vars =
    let add r s =
      try Spv.union (Mreg.find r rm) s with Not_found -> assert false
    in
    Sreg.fold add sreg Spv.empty
  in
  let quantify_v v f = wp_forall kn v.pv_pure f in
  Spv.fold quantify_v vars f

(* quantify over all references in ef
   ef : effect
   rm : region -> pvsymbol set
   f  : formula

   let ef = { rho1, ..., rhon }
   we collect in vars all variables involving these regions
   let vars = { v1, ..., vm }

     forall r1:ty(rho1). ... forall rn:ty(rhon).
     let v'1 = update v1 r1...rn in
     ...
     let v'm = update vm r1...rn in
     f[vi <- v'i]
*)
let quantify env rm ef f =
  let sreg = ef.E.writes in
  (* mreg: rho -> rho' *)
  let mreg =
    let add r m =
      let r' = create_vsymbol (id_clone r.R.r_tv.tv_name) (purify r.R.r_ty) in
      Mreg.add r r' m
    in
    Sreg.fold add sreg Mreg.empty
  in
  (* all program variables involving these regions *)
  let vars =
    let add r _ s =
      try Spv.union (Mreg.find r rm) s with Not_found -> assert false
    in
    Mreg.fold add mreg Spv.empty
  in
  (* s: v -> v' and vv': pv -> v', update_v *)
  let mreg, s, vv' =
    let add pv (mreg, s, vv') = match pv.pv_effect.vs_ty.ty_node with
      | Ty.Tyapp (ts, _) ->
          let mt = get_mtsymbol ts in
          if mt.mt_singleton then begin (* singleton type *)
            assert (Sreg.cardinal pv.pv_regions = 1);
            let r = Sreg.choose pv.pv_regions in
            (* a better name for r' *)
            let r' = create_vsymbol (id_clone pv.pv_name) (purify r.R.r_ty) in
            let mreg = Mreg.add r r' mreg in
            let ty = pv.pv_pure.vs_ty in
            let v' = create_vsymbol (id_clone pv.pv_name) ty in
            let cs = find_constructor env mt.mt_pure in
            let update = fs_app cs [t_var r'] ty in
            let vv' = Mpv.add pv (v', update) vv' in
            mreg, Mvs.add pv.pv_pure v' s, vv'
          end else begin
            eprintf "pv = %a@." print_pvsymbol pv;
            failwith "WP: update not yet implemented" (* assert false *)
          end
      | Ty.Tyvar _ ->
          assert false
    in
    Spv.fold add vars (mreg, Mvs.empty, Mpv.empty)
  in
  let f = unref env s f in
  let quantify_v' _pv (v', updatev) f =
    t_let_close v' updatev f
  in
  let f = Mpv.fold quantify_v' vv' f in
  let quantify_r _ r' f = wp_forall env r' f in
  Mreg.fold quantify_r mreg f

(* let quantify ?(all=false) env rm ef f = *)
(*   let r = quantify ~all env rm ef f in *)
(*   eprintf "@[<hov 2>quantify: all=%b ef=%a f=@[%a@] ==>@\n%a@]@." *)
(*     all E.print ef Pretty.print_term f Pretty.print_term r; *)
(*   r *)

let abstract_wp env rm ef (q',ql') (q,ql) =
  assert (List.length ql' = List.length ql);
  let quantify_res f' f res =
    let f = wp_implies f' f in
    let f = match res with
      (* | Some v when is_mutable_ty v.vs_ty -> *)
      (*          let v' = create_vsymbol (id_clone v.vs_name) (unref_ty env v.vs_ty) in *)
      (*          wp_forall v' (unref env (R.Rlocal v) v' f) *)
      | Some v ->
          wp_forall env v f
      | None ->
          f
    in
    quantify env rm ef f
  in
  let quantify_h (e',(x',f')) (e,(x,f)) =
    assert (ls_equal e' e);
    let res, f' = match x', x with
      | Some v', Some v -> Some v, t_subst (subst1 v' (t_var v)) f'
      | None, None -> None, f'
      | _ -> assert false
    in
    quantify_res f' f res
  in
  let f =
    let res, f = q and res', f' = q' in
    let f' =
      if is_arrow_ty res'.vs_ty then f'
      else t_subst (subst1 res' (t_var res)) f'
    in
    quantify_res f' f (Some res)
  in
  wp_ands (f :: List.map2 quantify_h ql' ql)

let opaque_wp env rm ef q' q =
  let lab = fresh_label env in
  let q' = post_map (old_label env lab) q' in
  let f = abstract_wp env rm ef q' q in
  erase_label env lab f

(*s [filter_post k q] removes exc. postconditions from [q] which do not
    appear in effect [ef] *)

let filter_post ef (q, ql) =
  let keep (ls, _) = Sexn.mem ls ef.E.raises in
  q, List.filter keep ql

let rec ls_assoc ls = function
  | [] -> raise Not_found
  | (ls', x) :: _ when ls_equal ls ls' -> x
  | _ :: r -> ls_assoc ls r

let default_exn_post ls = ls, (exn_v_result ls, t_true)

let default_post ty ef =
  (v_result ty, t_true),
  List.map default_exn_post (Sexn.elements ef.E.raises)

let rec assoc_handler x = function
  | [] -> raise Not_found
  | (y, h) :: _ when ls_equal x y -> h
  | _ :: hl -> assoc_handler x hl

(*s [saturate_post ef f q] makes a postcondition for a program of effect [ef]
    out of a normal postcondition [f] and the exc. postconditions from [q] *)

let saturate_post ef q (_, ql) =
  let set_post x = try x, ls_assoc x ql with Not_found -> default_exn_post x in
  let xs = Sexn.elements ef.E.raises in
  (q, List.map set_post xs)

(* maximum *)

let is_default_post = t_equal t_true

let sup ((q, ql) : post) (_, ql') =
  assert (List.length ql = List.length ql');
  let supx (x, (_,fa) as a) (x', _ as a') =
    assert (ls_equal x x');
    if is_default_post fa then a' else a
  in
  q, List.map2 supx ql ql'

(* post-condition for a loop body *)

let default_exns_post ef =
  let xs = Sexn.elements ef.E.raises in
  List.map default_exn_post xs

let term_at env lab t =
  t_app (find_ls ~pure:true env "at") [t; t_var lab] t.t_ty

let wp_expl l f =
  t_label ?loc:f.t_loc (("expl:"^l)::Split_goal.stop_split::f.t_label) f

let while_post_block env inv var lab e =
  let decphi = match var with
    | None ->
        t_true
    | Some (phi, None) ->
        let old_phi = term_at env lab phi in
        (* 0 <= old_phi and phi < old_phi *)
        wp_and (ps_app (find_ls ~pure:true env "infix <=")
                  [t_int_const "0"; old_phi])
               (ps_app (find_ls ~pure:true env "infix <")  [phi; old_phi])
    | Some (phi, Some r) ->
        ps_app r [phi; term_at env lab phi]
  in
  let decphi = wp_expl "loop variant decreases" decphi in
  let ql = default_exns_post e.expr_effect in
  let res = v_result e.expr_type in
  match inv with
    | None ->
        (res, decphi), ql
    | Some i ->
        (res, wp_and (wp_expl "loop invariant preservation" i) decphi), ql

let well_founded_rel = function
  | None -> t_true
  | Some (_,_r) -> t_true (* TODO: Papp (well_founded, [Tvar r], []) *)

(* Recursive computation of the weakest precondition *)

let wp_label ?loc f =
  if List.mem "WP" f.t_label then f
  else t_label ?loc ("WP"::f.t_label) f

let t_True env =
  fs_app (find_ls ~pure:true env "True") []
    (ty_app (find_ts ~pure:true env "bool") [])

(*
let add_expl msg f =
  t_label_add Split_goal.stop_split (t_label_add ("expl:"^msg) f)
*)

(*
  env : module_uc
  rm  : Spv.t Mreg.t (maps regions to pvsymbol sets)
*)

let rec wp_expr env rm e q =
  let lab = fresh_label env in
  let q = post_map (old_label env lab) q in
  let f = wp_desc env rm e q in
  let f = erase_label env lab f in
  let f = wp_label ~loc:e.expr_loc f in
  if Debug.test_flag debug then begin
    eprintf "@[--------@\n@[<hov 2>e = %a@]@\n" Pgm_pretty.print_expr e;
    eprintf "@[<hov 2>q = %a@]@\n" Pretty.print_term (snd (fst q));
    eprintf "@[<hov 2>f = %a@]@\n----@]@." Pretty.print_term f;
  end;
  f

and wp_desc env rm e q = match e.expr_desc with
  | Elogic t ->
      let (v, q), _ = q in
      t_subst_single v t q
  | Elocal v ->
      let (res, q), _ = q in
      t_subst (subst1 res (t_var v.pv_pure)) q
  | Eglobal { ps_kind = PSfun _ } ->
      let (_, q), _ = q in q
  | Eglobal { ps_kind = PSvar pv } ->
      let (v, q), _ = q in
      t_subst_single v (t_var pv.pv_pure) q
  | Eglobal { ps_kind = PSlogic } ->
      assert false
  | Efun (bl, t) ->
      let (_, q), _ = q in
      let f = wp_triple env rm bl t in
      wp_and q f
  | Elet (x, e1, e2) ->
      let w2 =
        let rm = add_binder x rm in
        wp_expr env rm e2 (filter_post e2.expr_effect q)
      in
      let v1 = v_result x.pv_pure.vs_ty in
      let t1 = t_label ~loc:e1.expr_loc ["let"] (t_var v1) in
      let q1 = v1, t_subst (subst1 x.pv_pure t1) w2 in
      let q1 = saturate_post e1.expr_effect q1 q in
      wp_expr env rm e1 q1
  | Eletrec (dl, e1) ->
      let w1 = wp_expr env rm e1 q in
      let wl = List.map (wp_recfun env rm) dl in
      wp_ands ~sym:true (w1 :: wl)
  | Eif (e1, e2, e3) ->
      let w2 = wp_expr env rm e2 (filter_post e2.expr_effect q) in
      let w3 = wp_expr env rm e3 (filter_post e3.expr_effect q) in
      let q1 = (* if result=True then w2 else w3 *)
        let res = v_result e1.expr_type in
        let test = t_equ (t_var res) (t_True env) in
        let test = wp_label ~loc:e1.expr_loc test in
        let q1 = t_if test w2 w3 in
        saturate_post e1.expr_effect (res, q1) q
      in
      wp_expr env rm e1 q1
  | Eloop ({ loop_invariant = inv; loop_variant = var }, e1) ->
      let wfr = well_founded_rel var in
      let lab = fresh_label env in
      let q1 = while_post_block env inv var lab e1 in
      let q1 = sup q1 q in (* exc. posts taken from [q] *)
      let we = wp_expr env rm e1 q1 in
      let we = erase_label env lab we in
      let w = match inv with
        | None ->
            wp_and wfr (quantify env rm e.expr_effect we)
        | Some i ->
            wp_and wfr
              (wp_and ~sym:true
                 (wp_expl "loop invariant init" i)
                 (quantify env rm e.expr_effect (wp_implies i we)))
        in
        w
  (* optimization for the particular case let _ = y in e *)
  | Ematch (_, [{ppat_pat = {pat_node = Term.Pwild}}, e]) ->
      wp_expr env rm e (filter_post e.expr_effect q)
  | Ematch (x, bl) ->
      let branch (p, e) =
        t_close_branch p.ppat_pat
          (wp_expr env rm e (filter_post e.expr_effect q))
      in
      let t = t_var x.pv_pure in
      t_case t (List.map branch bl)
  | Eabsurd ->
      t_false
  | Eraise (x, None) ->
      (* $wp(raise E, _, R) = R$ *)
      let _, ql = q in
      let _, f = assoc_handler x ql in f
  | Eraise (x, Some e1) ->
      (* $wp(raise (E e1), _, R) = wp(e1, R, R)$ *)
      let _, ql = q in
      let q1 = match assoc_handler x ql with
        | Some v, r -> (v, r), ql
        | None, _ -> assert false
      in
      let q1 = filter_post e1.expr_effect q1 in
      wp_expr env rm e1 q1
  | Etry (e1, hl) ->
      (* $wp(try e1 with E -> e2, Q, R) = wp(e1, Q, wp(e2, Q, R))$ *)
      let hwl =
        List.map
          (fun (x, v, h) ->
             let w = wp_expr env rm h (filter_post h.expr_effect q) in
             let v = option_map (fun v -> v.pv_pure) v in
             x, (v, w))
          hl
      in
      let make_post (q, ql) =
        let hpost (x, r) =
          x, try assoc_handler x hwl with Not_found -> r
        in
        q, List.map hpost ql
      in
      let q1 = saturate_post e1.expr_effect (fst q) q in
      let q1 = filter_post e1.expr_effect (make_post q1) in
      wp_expr env rm e1 q1
  | Efor (x, v1, d, v2, inv, e1) ->
      (* wp(for x = v1 to v2 do inv { I(x) } e1, Q, R) =
             v1 > v2  -> Q
         and v1 <= v2 ->     I(v1)
                         and forall S. forall i. v1 <= i <= v2 ->
                                                 I(i) -> wp(e1, I(i+1), R)
                                       and I(v2+1) -> Q                    *)
      let (res, q1), _ = q in
      let gt, le, incr = match d with
        | Ptree.To     ->
            find_ls ~pure:true env "infix >",
            find_ls ~pure:true env "infix <=", t_int_const  "1"
        | Ptree.Downto ->
            find_ls ~pure:true env "infix <",
            find_ls ~pure:true env "infix >=", t_int_const "-1"
      in
      let v1_gt_v2 = ps_app gt [t_var v1.pv_pure; t_var v2.pv_pure] in
      let v1_le_v2 = ps_app le [t_var v1.pv_pure; t_var v2.pv_pure] in
      let inv = match inv with Some inv -> inv | None -> t_true in
      let add = find_ls~pure:true env "infix +" in
      let wp1 =
        let xp1 = fs_app add [t_var x.pv_pure; incr] ty_int in
        let post = t_subst (subst1 x.pv_pure xp1) inv in
        let q1 = saturate_post e1.expr_effect (res, post) q in
        wp_expr env rm e1 q1
      in
      let f = wp_and ~sym:true
        (wp_expl "for loop initialization"
           (t_subst (subst1 x.pv_pure (t_var v1.pv_pure)) inv))
        (quantify env rm e.expr_effect
           (wp_and ~sym:true
              (wp_expl "for loop preservation"
                (wp_forall env x.pv_pure
                 (wp_implies
                    (wp_and (ps_app le [t_var v1.pv_pure; t_var x.pv_pure])
                            (ps_app le [t_var x.pv_pure;  t_var v2.pv_pure]))
                 (wp_implies inv wp1))))
              (let sv2 = fs_app add [t_var v2.pv_pure; incr] ty_int in
               wp_implies (t_subst (subst1 x.pv_pure sv2) inv) q1)))
      in
      wp_and ~sym:true (wp_implies v1_gt_v2 q1) (wp_implies v1_le_v2 f)

  | Eassert (Ptree.Aassert, f) ->
      let (_, q), _ = q in
      wp_and (wp_expl "assertion" f) q
  | Eassert (Ptree.Acheck, f) ->
      let (_, q), _ = q in
      wp_and ~sym:true (wp_expl "check" f) q
  | Eassert (Ptree.Aassume, f) ->
      let (_, q), _ = q in
      wp_implies f q
  | Elabel (lab, e1) ->
      let w1 = wp_expr env rm e1 q in
      erase_label env lab w1
  | Eany c ->
      (* TODO: propagate call labels into c.c_post *)
      let w = opaque_wp env rm c.c_effect c.c_post q in
      let p = wp_expl "precondition" c.c_pre in
      let p = t_label ~loc:e.expr_loc p.t_label p in
      wp_and p w

and wp_triple env rm bl (p, e, q) =
  let rm = add_binders bl rm in
  let q =
    let (v, q), l = q in
    (v, wp_expl "normal postcondition" q),
    List.map (fun (e, (v, q)) ->
                e, (v, wp_expl "exceptional postcondition" q)) l
  in
  let f = wp_expr env rm e q in
  let f = wp_implies p f in
  let f = wp_close env rm e.expr_effect f in
  wp_binders env bl f

and wp_recfun env rm (_, bl, _var, t) =
  wp_triple env rm bl t

let global_regions = ref Mreg.empty

let declare_global_regions pv = global_regions := add_binder pv !global_regions

let wp env e =
  let rm = !global_regions in
  wp_expr env rm e (default_post e.expr_type e.expr_effect)

let rec t_btop env t = match t.t_node with
  | Tif (f,t1,t2) -> let f = f_btop env f in
      t_label t.t_label (t_if_simp f (t_btop env t1) (t_btop env t2))
  | Tapp (ls, [t1;t2]) when ls_equal ls (find_ls ~pure:true env "andb") ->
      t_label t.t_label (t_and_simp (t_btop env t1) (t_btop env t2))
  | Tapp (ls, [t1;t2]) when ls_equal ls (find_ls ~pure:true env "orb") ->
      t_label t.t_label (t_or_simp (t_btop env t1) (t_btop env t2))
  | Tapp (ls, [t1]) when ls_equal ls (find_ls ~pure:true env "notb") ->
      t_label t.t_label (t_not_simp (t_btop env t1))
  | Tapp (ls, []) when ls_equal ls (find_ls ~pure:true env "True") ->
      t_label t.t_label t_true
  | Tapp (ls, []) when ls_equal ls (find_ls ~pure:true env "False") ->
      t_label t.t_label t_false
  | _ ->
      t_equ t (t_True env)

and f_btop env f = match f.t_node with
  | Tapp (ls, [{t_ty = Some {ty_node = Tyapp (ts, [])}} as l; r])
  when ls_equal ls ps_equ && ts_equal ts (find_ts ~pure:true env "bool") ->
      t_label_copy f (t_iff_simp (t_btop env l) (t_btop env r))
  | _ -> TermTF.t_map (fun t -> t) (f_btop env) f

let add_wp_decl ps f uc =
  let name = ps.ps_impure.ls_name in
  let s = "WP_" ^ name.id_string in
  let label = ["expl:correctness of " ^ name.id_string] in
  let id = id_fresh ~label ?loc:name.id_loc s in
  let f = f_btop uc f in
  let km = get_known (pure_uc uc) in
  let f = eval_match ~inline:inline_nonrec_linear km f in
  (* printf "wp: f=%a@." print_term f; *)
  let pr = create_prsymbol id in
  let d = create_prop_decl Pgoal pr f in
  add_pure_decl d uc

let decl uc = function
  | Pgm_ttree.Dlet (ps, e) ->
      Debug.dprintf debug "@[--effect %s-----@\n  %a@]@\n----------------@."
          ps.ps_impure.ls_name.id_string print_type_v e.expr_type_v;
      let f = wp uc e in
      Debug.dprintf debug "wp = %a@\n----------------@." Pretty.print_term f;
      add_wp_decl ps f uc
  | Pgm_ttree.Dletrec dl ->
      let add_one uc (ps, def) =
        let f = wp_recfun uc !global_regions def in
        Debug.dprintf debug "wp %s = %a@\n----------------@."
           ps.ps_impure.ls_name.id_string Pretty.print_term f;
        add_wp_decl ps f uc
      in
      List.fold_left add_one uc dl
  | Pgm_ttree.Dparam _ ->
      uc

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)
