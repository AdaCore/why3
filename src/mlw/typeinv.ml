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
open Ity
open Expr
open Pdecl

let ls_valid =
  let v = create_tvsymbol (id_fresh "a") in
  create_psymbol (id_fresh "valid") [ty_var v]

let its_solid s =
  not s.its_fragile && (* no need to go any further *)
  List.for_all (fun f -> f.its_frozen) s.its_arg_flg &&
  List.for_all (fun f -> f.its_frozen) s.its_reg_flg

let is_trusted_constructor _kn ls =
  ls.ls_constr > 0 &&
  match (Opt.get ls.ls_value).ty_node with
  | Tyapp (s,_) -> not (its_solid (restore_its s))
  | _ -> assert false

let is_trusted_projection kn ls ity =
  ls.ls_constr = 0 &&
  try let rs = restore_rs ls in
      if rs.rs_field = None then false else
      match (List.hd rs.rs_cty.cty_args).pv_ity.ity_node with
      | Ityreg {reg_its = s} | Ityapp (s,_,_) ->
          not (its_solid s) &&
          (* we don't trust projections of sum types that produce
             fragile values, since they may break cap_of_term *)
          (not (ity_fragile ity) ||
            List.length (Eval_match.ts_constructors kn s.its_ts) <= 1)
      | _ -> assert false
  with Not_found -> false

let is_trusted_projection_t kn ls t = match t.t_ty with
  | Some ty -> is_trusted_projection kn ls (ity_of_ty_pure ty)
  | None -> false

(* Integer-indexed "pins" represent individual values whose
   invariant may be broken. Fresh pins are assigned to values
   bottom-up, and the canonical representative pin in a UF class
   is the minimal one. Thus, a greater pin can never be reached
   from a lesser pin. Each pin is associated to a list of fresh
   variables that correspond to "temporary fields". Committing
   a pin means that we prove that the temporary fields satisfy
   the invariant and then assume that the temporary fields are
   equal to the respective projections.

   Recursive "caps" represent deconstructible values from which
   pins can be reached. Each variable is associated to a cap.
   A cap is either a committed value, a pin (a non-committed
   record with a breakable invariant), a constructible value
   (characterized by the set of possible constructors), or
   a non-free record with an unbreakable invariant. *)

type cap =
  | V                   (* valid *)
  | P of int            (* pin *)
  | C of cap list Mls.t (* algebraic type *)
  | R of cap Mls.t      (* non-free unbreakable record *)

let isV = function V -> true | _ -> false

let mkP n =
  if n = 0 then V else P n

let mkC css =
  let chk _ l = List.for_all isV l in
  if Mls.for_all chk css then V else C css

let mkR pjs =
  let chk _ c = isV c in
  if Mls.for_all chk pjs then V else R pjs

let new_index =
  let c = ref 0 in
  fun () -> incr c; !c

(* Stage I - Inspect: detect values that must be committed and provide
   the necessary ls_valid applications. *)

type pin_inspect = {
  p_fields : cap Mls.t;             (* record fields *)
  p_stem   : (term * pattern) list; (* deconstruction from a root *)
  p_leaf   : term;                  (* term we can be reached from *)
}

let gl_caps = (Wvs.create 7 : (cap * pin_inspect Mint.t) Wvs.t)

let extract_field cs f ty tyl =
  let pat_arg ({pv_vs = v} as a) ty = if pv_equal a f
    then pat_var (create_vsymbol (id_clone v.vs_name) ty)
    else pat_wild ty in
  let pl = List.map2 pat_arg cs.rs_cty.cty_args tyl in
  let pat = pat_app (ls_of_rs cs) pl ty in
  pat, t_var (Svs.choose pat.pat_vars)

let add_gl_cap kn v =
  let rp = ref Mint.empty in
  let rec down stem leaf ty = match ty.ty_node with
    | Tyvar _ -> V
    | Tyapp (s,tl) ->
        let s = restore_its s in
        if its_solid s then V else
        let d = find_its_defn kn s in
        let sbs = ts_match_args s.its_ts tl in
        if s.its_nonfree then if s.its_fragile then (* breakable record *)
          let add_field m f =
            let vf = fd_of_rs f in
            let ty = Ty.ty_inst sbs vf.pv_vs.vs_ty in
            let leaf = fs_app (ls_of_rs f) [leaf] ty in
            Mls.add (ls_of_rs f) (down stem leaf ty) m in
          let pjs = List.fold_left add_field Mls.empty d.itd_fields in
          let pin = {p_fields = pjs; p_stem = stem; p_leaf = leaf} in
          let n = new_index () in
          rp := Mint.add n pin !rp;
          mkP n
        else (* unbreakable record *)
          let add_field m f =
            let vf = fd_of_rs f in
            let ty = Ty.ty_inst sbs vf.pv_vs.vs_ty in
            let leaf = fs_app (ls_of_rs f) [leaf] ty in
            Mls.add (ls_of_rs f) (down stem leaf ty) m in
          mkR (List.fold_left add_field Mls.empty d.itd_fields)
        else if List.length d.itd_constructors == 1 then (* record type *)
          let add_field m f = Mpv.add (fd_of_rs f) (ls_of_rs f) m in
          let pjm = List.fold_left add_field Mpv.empty d.itd_fields in
          let add_constr m c =
            let inst f = Ty.ty_inst sbs f.pv_vs.vs_ty in
            let tyl = List.map inst c.rs_cty.cty_args in
            let conv_field f ty_f =
              let leaf = match Mpv.find_opt f pjm with
                | Some pj -> fs_app pj [leaf] ty_f
                | None -> t_case_close leaf [extract_field c f ty tyl] in
              down stem leaf ty_f in
            let fdl = List.map2 conv_field c.rs_cty.cty_args tyl in
            Mls.add (ls_of_rs c) fdl m in
          mkC (List.fold_left add_constr Mls.empty d.itd_constructors)
        else (* sum type *)
          let add_constr m c =
            let inst f = Ty.ty_inst sbs f.pv_vs.vs_ty in
            let tyl = List.map inst c.rs_cty.cty_args in
            let conv_field f ty_f =
              let pat, t = extract_field c f ty tyl in
              down ((leaf, pat)::stem) t ty_f in
            let fdl = List.map2 conv_field c.rs_cty.cty_args tyl in
            Mls.add (ls_of_rs c) fdl m in
          mkC (List.fold_left add_constr Mls.empty d.itd_constructors)
  in
  let c = down [] (t_var v) v.vs_ty in
  Wvs.set gl_caps v (c, !rp);
  c, !rp

let inspect kn tl =
  let rpins = ref Mint.empty in
  let rcommit = ref Mint.empty in
  let rec cap_valid = function
    | V -> ()
    | P n ->
        let pin = Mint.find n !rpins in
        Mls.iter (fun _ c -> cap_valid c) pin.p_fields;
        rcommit := Mint.add n pin !rcommit
    | C css -> Mls.iter (fun _ fl -> List.iter cap_valid fl) css
    | R pjs -> Mls.iter (fun _ c -> cap_valid c) pjs
  in
  let rec cap_join c1 c2 = match c1, c2 with
    | V, c | c, V ->
        cap_valid c; V
    | P n1, P n2 ->
        if n1 = n2 then c1 else begin
          cap_valid c1; cap_valid c2; V
        end
    | C s1, C s2 ->
        let join _ l1 l2 = Some (List.map2 cap_join l1 l2) in
        mkC (Mls.union join s1 s2)
    | R s1, R s2 ->
        let join _ c1 c2 = Some (cap_join c1 c2) in
        mkR (Mls.union join s1 s2)
    | _ -> assert false
  in
  let rec add_pat caps c p =
    if isV c then
      Mvs.set_union caps (Mvs.map (fun () -> V) p.pat_vars)
    else match p.pat_node with
    | Pwild -> caps
    | Pvar v -> Mvs.add v c caps
    | Papp (cs,pl) -> begin match c with
        | C css -> begin match Mls.find_opt cs css with
            | Some cl -> List.fold_left2 add_pat caps cl pl
            | None -> caps (* impossible branch *) end
        | _ -> assert false (* can never happen *) end
    | Por (p,_) -> cap_valid c; add_pat caps V p
    | Pas (p,v) -> Mvs.add v c (add_pat caps c p)
  in
  let rec unwind c pjl0 = match c, pjl0 with
    | _, [] -> c
    | V, _ -> V
    | P n, pj::pjl ->
        let pin = Mint.find n !rpins in
        unwind (Mls.find pj pin.p_fields) pjl
    | C css, pj::pjl when Mls.cardinal css = 1 ->
        let cs, fl = Mls.choose css in
        let fdl = Eval_match.cs_fields kn cs in
        let c = Eval_match.select_field pj fdl fl in
        unwind c pjl
    | C css, pj::pjl ->
        let ty = List.hd pj.ls_args in
        let add_branch fdl fl cj =
          let c = Eval_match.select_field pj fdl fl in
          Some (Opt.fold cap_join (unwind c pjl) cj) in
        let csl = Eval_match.ty_constructors kn ty in
        let add_branch (cs, fdl) acc =
          match Mls.find_opt cs css with
          | Some fl -> add_branch fdl fl acc
          | None -> acc in
        Opt.get (List.fold_right add_branch csl None)
    | R pjs, pj::pjl ->
        unwind (Mls.find pj pjs) pjl
  in
  let rec down caps pjl t = match t.t_node with
    | Tvar v -> (* projection propagation *)
        let c = try Mvs.find v caps with Not_found ->
          let c, pins = try Wvs.find gl_caps v with
            | Not_found -> add_gl_cap kn v in
          rpins := Mint.set_union pins !rpins;
          c in
        unwind c pjl
    | Tconst _ -> V
    | Tapp (ls,[t1;t2]) when ls_equal ls ps_equ ->
        let c1 = down caps pjl t1 in
        let c2 = down caps pjl t2 in
        ignore (cap_join c1 c2); V
    | Tapp (ls,[t1]) when is_trusted_projection_t kn ls t ->
        down caps (ls::pjl) t1
    | Tapp (ls,tl) when is_trusted_constructor kn ls ->
        begin match pjl with
        | pj::pjl ->
            let fdl = Eval_match.cs_fields kn ls in
            let t = Eval_match.select_field pj fdl tl in
            down caps pjl t
        | [] ->
            let cl = List.map (down caps []) tl in
            mkC (Mls.singleton ls cl) end
    | Tapp (_,tl) ->
        let t_valid t = cap_valid (down caps [] t) in
        List.iter t_valid tl; V
    | Tif (t0,t1,t2) ->
        let _  = down caps [] t0 in
        let c1 = down caps pjl t1 in
        let c2 = down caps pjl t2 in
        cap_join c1 c2
    | Tlet (t0,tb) ->
        let c0 = down caps [] t0 in
        let v, t1 = t_open_bound tb in
        let caps = Mvs.add v c0 caps in
        down caps pjl t1
    | Tcase (t0,bl) ->
        let c0 = down caps [] t0 in
        let add_branch b cj =
          let p, t1 = t_open_branch b in
          let caps = add_pat caps c0 p in
          let c = down caps pjl t1 in
          Some (Opt.fold cap_join c cj) in
        Opt.get (List.fold_right add_branch bl None)
    | Teps tb ->
        let v, f = t_open_bound tb in
        let caps = Mvs.add v V caps in
        ignore (down caps [] f); V
    | Tquant (_,tq) ->
        let vl, tt, f = t_open_quant tq in
        let add caps v = Mvs.add v V caps in
        let caps = List.fold_left add caps vl in
        (* NOTE: should we commit triggers? *)
        let down t = ignore (down caps [] t) in
        List.iter (List.iter down) tt; down f; V
    | Tbinop (_,f1,f2) ->
        ignore (down caps [] f1);
        ignore (down caps [] f2); V
    | Tnot f ->
        ignore (down caps [] f); V
    | Ttrue | Tfalse -> V
  in
  let add_term t = ignore (down Mvs.empty [] t) in
  List.iter add_term tl;
  let commit pin =
    let f = ps_app ls_valid [pin.p_leaf] in
    let add f (t, p) = t_case_close t
      [p, f; pat_wild p.pat_ty, t_true] in
    List.fold_left add f pin.p_stem in
  Mint.values (Mint.map commit !rcommit)

(* Stage II - Inject: replace unsafe projections with
   temporary fields and expand ls_valid wherever needed. *)

type pin_inject = {
  p_vars : (vsymbol * cap) Mls.t; (* temporary fields *)
  p_inv  : term list;             (* instantiated invariant *)
}

let add_var kn pins vl v =
  let rv = ref vl in
  let rp = ref pins in
  let rec down ty = match ty.ty_node with
    | Tyvar _ -> V
    | Tyapp (s,tl) ->
        let s = restore_its s in
        if its_solid s then V else
        let d = find_its_defn kn s in
        let sbs = Ty.ts_match_args s.its_ts tl in
        if s.its_nonfree then if s.its_fragile then (* breakable record *)
          let bn = v.vs_name.id_string in
          let add_field (m,mv) f =
            let vf = fd_of_rs f in
            let ty = Ty.ty_inst sbs vf.pv_vs.vs_ty in
            let nm = bn ^ "_" ^ f.rs_name.id_string in
            let v = create_vsymbol (id_fresh nm) ty in
            rv := v :: !rv;
            let mv = Mvs.add vf.pv_vs (t_var v) mv in
            Mls.add (ls_of_rs f) (v, down ty) m, mv in
          let pjs, mv = List.fold_left add_field
                            (Mls.empty, Mvs.empty) d.itd_fields in
          let inv = List.map (t_ty_subst sbs mv) d.itd_invariant in
          let pin = {p_vars = pjs; p_inv = inv} in
          let n = new_index () in
          rp := Mint.add n pin !rp;
          mkP n
        else (* unbreakable record *)
          let add_field m f =
            let vf = fd_of_rs f in
            let ty = Ty.ty_inst sbs vf.pv_vs.vs_ty in
            Mls.add (ls_of_rs f) (down ty) m in
          mkR (List.fold_left add_field Mls.empty d.itd_fields)
        else (* constructible type *)
          let add_constr m c =
            let field vf = down (Ty.ty_inst sbs vf.pv_vs.vs_ty) in
            Mls.add (ls_of_rs c) (List.map field c.rs_cty.cty_args) m in
          mkC (List.fold_left add_constr Mls.empty d.itd_constructors)
  in
  let c = down v.vs_ty in
  (* do not inline *) c, !rp, !rv

let add_cap v c caps =
  if isV c then caps else Mvs.add v c caps

let rec get_index uf n =
  if n = 0 then 0 else
  match Mint.find_opt n uf with
  | Some n -> get_index uf n
  | None -> n

let cap_valid uf c =
  let rec down = function
    | V -> ()
    | P n -> if get_index uf n <> 0 then raise Exit
    | C css -> Mls.iter (fun _ fl -> List.iter down fl) css
    | R pjs -> Mls.iter (fun _ c -> down c) pjs in
  try down c; true with Exit -> false

let rec cap_join uf c1 c2 = match c1, c2 with
  | V, c | c, V ->
      assert (cap_valid uf c); V
  | P n1, P n2 ->
      let n1 = get_index uf n1 in
      let n2 = get_index uf n2 in
      assert (n1 = n2);
      mkP n1
  | C s1, C s2 ->
      let join _ l1 l2 = Some (List.map2 (cap_join uf) l1 l2) in
      mkC (Mls.union join s1 s2)
  | R s1, R s2 ->
      let join _ c1 c2 = Some (cap_join uf c1 c2) in
      mkR (Mls.union join s1 s2)
  | _ -> assert false

let rec add_pat uf caps c p =
  if isV c then caps else
  match p.pat_node with
  | Pwild -> caps
  | Pvar v -> Mvs.add v c caps
  | Papp (cs,pl) -> begin match c with
      | C css -> begin match Mls.find_opt cs css with
          | Some cl -> List.fold_left2 (add_pat uf) caps cl pl
          | None -> caps (* impossible branch *) end
      | _ -> assert false (* can never happen *) end
  | Por _ -> assert (cap_valid uf c); caps
  | Pas (p,v) -> Mvs.add v c (add_pat uf caps c p)

let cap_of_term kn uf pins caps t =
  let rec unroll t = function
    | (pj,t0)::pjl ->
        let t = t_app pj [t] t0.t_ty in
        unroll (t_attr_copy t0 t) pjl
    | []  -> t in
  let rec unwind t c pjl0 = match c, pjl0 with
    | _, [] -> t, c
    | V, _ -> unroll t pjl0, V
    | P n, (pj,t0)::pjl ->
        let n = get_index uf n in
        if n = 0 then unroll t pjl0, V
        else let pin = Mint.find n pins in
          let v, c = Mls.find pj pin.p_vars in
          unwind (t_attr_copy t0 (t_var v)) c pjl
    | C css, (pj,t0)::pjl when Mls.cardinal css = 1 ->
        let cs, fl = Mls.choose css in
        let fdl = Eval_match.cs_fields kn cs in
        let c = Eval_match.select_field pj fdl fl in
        let t = t_app pj [t] t0.t_ty in
        unwind (t_attr_copy t0 t) c pjl
    | C css, (pj,t0)::pjl ->
        let ty = Opt.get t.t_ty in
        let sbs = Ty.ty_match_args ty in
        let v0 = create_vsymbol (id_fresh "q") (Opt.get t0.t_ty) in
        let t0 = t_attr_copy t0 (t_var v0) and p0 = pat_var v0 in
        let add_branch cs fdl fl (bl, cj) =
          let mk_pat fd_ty fd = match fd with
            | Some ls when ls_equal pj ls -> p0
            | _ -> pat_wild (Ty.ty_inst sbs fd_ty) in
          let pl = List.map2 mk_pat cs.ls_args fdl in
          let c = Eval_match.select_field pj fdl fl in
          let t0, c = unwind t0 c pjl in
          let b = t_close_branch (pat_app cs pl ty) t0 in
          b::bl, Some (Opt.fold (cap_join uf) c cj) in
        let csl = Eval_match.ty_constructors kn ty in
        let add_branch (cs, fdl) acc =
          match Mls.find_opt cs css with
          | Some fl -> add_branch cs fdl fl acc
          | None -> acc in
        let bb = match Mls.choose css with
          | {ls_constr = len}, _ when len > Mls.cardinal css ->
              let v = create_vsymbol (id_fresh "q") ty in
              [t_close_branch (pat_var v) (unroll (t_var v) pjl0)]
          | _ -> [] in
        let bl, c = List.fold_right add_branch csl (bb, None) in
        t_case t bl, Opt.get c
    | R pjs, (pj,t0)::pjl ->
        let c = Mls.find pj pjs in
        let t = t_app pj [t] t0.t_ty in
        unwind (t_attr_copy t0 t) c pjl
  in
  let rec down caps pjl t = match t.t_node with
    | Tvar v -> (* projection propagation *)
        unwind t (Mvs.find_def V v caps) pjl
    | Tconst _ -> (* constants are valid *)
        unroll t pjl, V
    | Tapp (ls,[t1;t2]) when ls_equal ls ps_equ ->
        let t1, c1 = down caps pjl t1 in
        let t2, c2 = down caps pjl t2 in
        ignore (cap_join uf c1 c2);
        t_attr_copy t (t_equ t1 t2), V
    | Tapp (ls,[t1]) when is_trusted_projection_t kn ls t ->
        down caps ((ls,t)::pjl) t1
    | Tapp (ls,tl) when is_trusted_constructor kn ls ->
        begin match pjl with
        | (pj,t0)::pjl ->
            let fdl = Eval_match.cs_fields kn ls in
            let t = Eval_match.select_field pj fdl tl in
            down caps pjl (t_attr_copy t0 t)
        | [] ->
            let tl, cl = List.split (List.map (down caps []) tl) in
            let t = t_attr_copy t (t_app ls tl t.t_ty) in
            t, mkC (Mls.singleton ls cl) end
    | Tapp (ls,tl) ->
        let tl = List.map (fun t ->
          let t, c = down caps [] t in
          assert (cap_valid uf c); t) tl in
        unroll (t_attr_copy t (t_app ls tl t.t_ty)) pjl, V
    | Tif (t0,t1,t2) ->
        let t0, _  = down caps [] t0 in
        let t1, c1 = down caps pjl t1 in
        let t2, c2 = down caps pjl t2 in
        t_attr_copy t (t_if t0 t1 t2), cap_join uf c1 c2
    | Tlet (t0,tb) ->
        let t0, c0 = down caps [] t0 in
        let v, t1 = t_open_bound tb in
        let caps = add_cap v c0 caps in
        let t1, c1 = down caps pjl t1 in
        t_attr_copy t (t_let_close v t0 t1), c1
    | Tcase (t0,bl) ->
        let t0, c0 = down caps [] t0 in
        let add_branch b (bl, cj) =
          let p, t1 = t_open_branch b in
          let caps = add_pat uf caps c0 p in
          let t1, c = down caps pjl t1 in
          let b = t_close_branch p t1 in
          b::bl, Some (Opt.fold (cap_join uf) c cj) in
        let bl, c = List.fold_right add_branch bl ([], None) in
        t_attr_copy t (t_case t0 bl), Opt.get c
    | Teps tb ->
        let v, f = t_open_bound tb in
        let f, _ = down caps [] f in
        unroll (t_attr_copy t (t_eps_close v f)) pjl, V
    | Tquant (q,tq) ->
        let vl, tt, t0 = t_open_quant tq in
        let down t = fst (down caps [] t) in
        let tt = List.map (List.map down) tt in
        let tq = t_close_quant vl tt (down t0) in
        t_attr_copy t (t_quant q tq), V
    | Tbinop (op,f1,f2) ->
        let f1, _ = down caps [] f1 in
        let f2, _ = down caps [] f2 in
        t_attr_copy t (t_binary op f1 f2), V
    | Tnot f ->
        let f, _ = down caps [] f in
        t_attr_copy t (t_not f), V
    | Ttrue | Tfalse ->
        t, V
  in
  down caps [] t

let find_term_fields kn cs t =
  let ty = Opt.get t.t_ty in
  let sbs = Ty.ty_match_args ty in
  let fdl = Eval_match.cs_fields kn cs in
  let add_pat ty (pl,pll) =
    let pw = pat_wild (Ty.ty_inst sbs ty) in
    let pv = pat_var (create_vsymbol (id_fresh "v") pw.pat_ty) in
    pw :: pl, (pv :: pl) :: List.map (fun pl -> pw :: pl) pll in
  let _, pll = List.fold_right add_pat cs.ls_args ([],[]) in
  let conv pl = function
    | Some pj -> t_app_infer pj [t]
    | None ->
        let p = pat_app cs pl ty in
        let v = Svs.choose p.pat_vars in
        t_case_close t [p, t_var v] in
  List.map2 conv pll fdl

let cap_equality kn uf pins f t1 c1 t2 c2 =
  let rec commit t c fl uf = match c with
    | V -> fl, uf
    | P n ->
        let n = get_index uf n in
        if n = 0 then fl, uf else
        let p = Mint.find n pins in
        let uf = Mint.add n 0 uf in
        let add pj (v,c) (fl,uf) =
          let tv = t_var v in
          let t = t_app_infer pj [t] in
          let fl, uf = commit tv c fl uf in
          t_equ tv t :: fl, uf in
        Mls.fold add p.p_vars (fl,uf)
    | C css when (fst (Mls.choose css)).ls_constr = 1 ->
        (* css cannot be empty and has at most one elt *)
        let cs, cl = Mls.choose css in
        let tl = find_term_fields kn cs t in
        let add t c (fl, uf) = commit t c fl uf in
        List.fold_right2 add tl cl (fl, uf)
    | C css ->
        let ty = Opt.get t.t_ty in
        let sbs = Ty.ty_match_args ty in
        let branch cs cl bl =
          let add ty c (pl,fl,uf) =
            let v = create_vsymbol (id_fresh "v") (ty_inst sbs ty) in
            let fl', uf = commit (t_var v) c fl uf in
            let p = if fl' == fl then pat_wild v.vs_ty else pat_var v in
            p::pl, fl', uf in
          let pl, fl, _ = List.fold_right2 add cs.ls_args cl ([],[],uf) in
          t_close_branch (pat_app cs pl ty) (t_and_l fl) :: bl in
        let bb = match Mls.choose css with
          | {ls_constr = len}, _ when len > Mls.cardinal css ->
              [t_close_branch (pat_wild ty) t_true]
          | _ -> [] in
        t_case t (Mls.fold branch css bb) :: fl, uf
    | R pjs ->
        let add pj c (fl,uf) = commit (t_app_infer pj [t]) c fl uf in
        Mls.fold add pjs (fl,uf)
  in
  let rec down t1 c1 t2 c2 fl uf = match c1, c2 with
    | V, _ -> commit t2 c2 fl uf
    | _, V -> commit t1 c1 fl uf
    | P n1, P n2 ->
        let n1 = get_index uf n1 in
        let n2 = get_index uf n2 in
        if n1 = n2 then fl, uf else
        if n1 = 0 then commit t2 (mkP n2) fl uf else
        if n2 = 0 then commit t1 (mkP n1) fl uf else
        let p1 = Mint.find n1 pins in
        let p2 = Mint.find n2 pins in
        let uf = if n1 < n2 then
          Mint.add n2 n1 uf else Mint.add n1 n2 uf in
        let add _pj (v1,c1) (v2,c2) (fl,uf) =
          let t1 = t_var v1 and t2 = t_var v2 in
          let fl, uf = down t1 c1 t2 c2 fl uf in
          t_equ t1 t2 :: fl, uf in
        Mls.fold2_inter add p1.p_vars p2.p_vars (fl,uf)
    | C css1, C css2 when (fst (Mls.choose css1)).ls_constr = 1 ->
        (* css1 and css2 cannot be empty and have at most one elt *)
        let cs, cl1 = Mls.choose css1 in
        let _,  cl2 = Mls.choose css2 in
        let tl1 = find_term_fields kn cs t1 in
        let tl2 = find_term_fields kn cs t2 in
        let rec add tl1 cl1 tl2 cl2 acc = match tl1,cl1,tl2,cl2 with
          | t1::tl1, c1::cl1, t2::tl2, c2::cl2 ->
              let fl, uf = add tl1 cl1 tl2 cl2 acc in
              down t1 c1 t2 c2 fl uf
          | _ -> acc in
        add tl1 cl1 tl2 cl2 (fl,uf)
    | C _css1, C _css2 ->
        assert false (* TODO *)
    | R pjs1, R pjs2 ->
        let add pj c1 c2 (fl,uf) =
          let t1 = t_app_infer pj [t1] in
          let t2 = t_app_infer pj [t2] in
          down t1 c1 t2 c2 fl uf in
        Mls.fold2_inter add pjs1 pjs2 (fl,uf)
    | _ -> assert false (* never *) in
  let fl, uf = down t1 c1 t2 c2 [] uf in
  t_and_l (f :: fl), uf

let uf_inter uf1 uf2 =
  let uf1 = Mint.map (get_index uf1) uf1 in
  let uf2 = Mint.map (get_index uf2) uf2 in
  let inter n m1 m2 acc =
    if m1 = m2 then acc else
    let easy = if m1 < m2
      then get_index uf1 m2 = m1
      else get_index uf2 m1 = m2 in
    if easy then acc else
    let inner b = Some (match b with
      | Some m -> min m n
      | None -> n) in
    let outer b = Some (match b with
      | Some m -> Mint.change inner m2 m
      | None -> Mint.singleton m2 n) in
    Mint.change outer m1 acc in
  let map = Mint.fold2_inter inter uf1 uf2 Mint.empty in
  let inter n m1 m2 =
    if m1 = m2 then Some m1 else
    try let m = Mint.find m2 (Mint.find m1 map) in
        if m = n then None else Some m
    with Not_found -> Some (max m1 m2) in
  Mint.inter inter uf1 uf2

let rec inject kn uf pins caps pos f = match f.t_node with
  | Tvar _ | Tconst _ | Teps _ -> assert false (* never *)
  | Tapp (ls,[t]) when pos && ls_equal ls ls_valid ->
      let _, c = cap_of_term kn uf pins caps t in
      let n = match c with
        | V -> 0
        | P n -> get_index uf n
        | _ -> assert false (* never *) in
      if n = 0 then t_true, uf else
      let p = Mint.find n pins in
      let check _ (_,c) = assert (cap_valid uf c) in
      Mls.iter check p.p_vars;
      let inv = List.map (t_attr_copy f) p.p_inv in
      t_and_asym_l inv, uf
  | Tapp (ls,[t]) when not pos && ls_equal ls ls_valid ->
      let t, c = cap_of_term kn uf pins caps t in
      let n = match c with
        | V -> 0
        | P n -> get_index uf n
        | _ -> assert false (* never *) in
      if n = 0 then t_true, uf else
      let p = Mint.find n pins in
      let uf = Mint.add n 0 uf in
      let add pj (v,c) fl =
        assert (cap_valid uf c);
        let t = t_app_infer pj [t] in
        t_equ (t_var v) t :: fl in
      t_attr_copy f (t_and_l (Mls.fold add p.p_vars [])), uf
  | Tapp (ls,[t1;t2]) when not pos && ls_equal ls ps_equ ->
      let t1, c1 = cap_of_term kn uf pins caps t1 in
      let t2, c2 = cap_of_term kn uf pins caps t2 in
      let f = t_attr_copy f (t_equ t1 t2) in
      cap_equality kn uf pins f t1 c1 t2 c2
  | _ when Sattr.mem annot_attr f.t_attrs ->
      fst (cap_of_term kn uf pins caps f), uf
  | Tapp _ ->
      fst (cap_of_term kn uf pins caps f), uf
  | Tif (f0,f1,f2) ->
      let f0, _ = cap_of_term kn uf pins caps f0 in
      let f1, uf1 = inject kn uf pins caps pos f1 in
      let f2, uf2 = inject kn uf pins caps pos f2 in
      t_attr_copy f (t_if f0 f1 f2), uf_inter uf1 uf2
  | Tlet (t0,fb) ->
      let t0, c0 =  cap_of_term kn uf pins caps t0 in
      let v, f1 = t_open_bound fb in
      let caps = add_cap v c0 caps in
      let f1, uf = inject kn uf pins caps pos f1 in
      t_attr_copy f (t_let_close v t0 f1), uf
  | Tcase (t0,bl) ->
      let t0, c0 = cap_of_term kn uf pins caps t0 in
      let add_branch b (bl, ufj) =
        let p, f1 = t_open_branch b in
        let caps = add_pat uf caps c0 p in
        let f1, uf1 = inject kn uf pins caps pos f1 in
        let b = t_close_branch p f1 in
        b::bl, Some (Opt.fold uf_inter uf1 ufj) in
      let bl, uf = List.fold_right add_branch bl ([], None) in
      t_attr_copy f (t_case t0 bl), Opt.get uf
  | Tquant (q,fq) ->
      let vl, tt, f0 = t_open_quant fq in
      let down t = fst (cap_of_term kn uf pins caps t) in
      let tt = List.map (List.map down) tt in
      let valid = match q with
        | Tforall -> not pos
        | Texists -> pos in
      let caps, pins, vl =
        if valid then caps, pins, vl else
        let add v (caps, pins, vl) =
          let c, pins, vl = add_var kn pins vl v in
          add_cap v c caps, pins, v::vl in
        List.fold_right add vl (caps, pins, []) in
      let f0, uf = inject kn uf pins caps pos f0 in
      let f0 = t_quant_close_simp q vl tt f0 in
      t_attr_copy f f0, uf
  | Tbinop (Tand,f1,f2) ->
      let f1, uf1 = inject kn uf  pins caps pos f1 in
      let f2, uf2 = inject kn uf1 pins caps pos f2 in
      t_attr_copy f (t_and f1 f2), uf2
  | Tbinop (Timplies,f1,f2) ->
      let f1, uf1 = inject kn uf  pins caps (not pos) f1 in
      let f2, _   = inject kn uf1 pins caps pos f2 in
      t_attr_copy f (t_implies f1 f2), uf
  | Tbinop (Tor,f1,f2) ->
      let f1, uf1 = inject kn uf pins caps pos f1 in
      let f2, uf2 = inject kn uf pins caps pos f2 in
      t_attr_copy f (t_or f1 f2), uf_inter uf1 uf2
  | Tbinop (Tiff,_,_) ->
      fst (cap_of_term kn uf pins caps f), uf
  | Tnot f1 ->
      let f1, _ = inject kn uf pins caps (not pos) f1 in
      t_attr_copy f (t_not f1), uf
  | Ttrue | Tfalse ->
      f, uf

let inject kn f =
  fst (inject kn Mint.empty Mint.empty Mvs.empty true f)
