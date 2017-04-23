(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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

(* helper functions for algebraic types *)

let ls_of_rs s = match s.rs_logic with
  RLls ls -> ls | _ -> assert false

let is_projection ls = ls.ls_constr = 0 &&
  try (restore_rs ls).rs_field <> None
  with Not_found -> false

let find_constructors_ts kn ({ts_name = id} as ts) =
  let rec find = function
    | {d_news = s}::dl when not (Mid.mem id s) -> find dl
    | {d_node = Ddata dl}::_ -> List.assq ts dl
    | _ -> [] in
  find (Mid.find id kn).pd_pure

let find_constructors kn ty = match ty.ty_node with
  | Tyapp (ts, _) -> find_constructors_ts kn ts
  | _ -> []

let find_logic_definition kn ({ls_name = id} as ls) =
  let rec find = function
    | {d_news = s}::dl when not (Mid.mem id s) -> find dl
    | {d_node = Dlogic dl}::_ -> Some (List.assq ls dl)
    | _ -> None in
  find (Mid.find id kn).pd_pure

let find_constructor_fields kn cs =
  let ty = Opt.get cs.ls_value in
  try List.assq cs (find_constructors kn ty)
  with Not_found -> assert false

let find_projection_field pj tl pjl =
  let rec find tl pjl = match tl, pjl with
    | t::_, Some ls::_ when ls_equal pj ls -> t
    | _::tl, _::pjl -> find tl pjl
    | _ -> assert false in
  find tl pjl

let apply_projection kn pj cs tl =
  find_projection_field pj tl (find_constructor_fields kn cs)

(* Part I - Invariant handling *)

let ls_valid =
  let v = create_tvsymbol (id_fresh "a") in
  create_psymbol (id_fresh "valid") [ty_var v]

let its_solid s =
  not s.its_fragile && (* no need to go any further *)
  List.for_all (fun f -> f.its_frozen) s.its_arg_flg &&
  List.for_all (fun f -> f.its_frozen) s.its_reg_flg

let is_fragile_constructor ls =
  ls.ls_constr > 0 &&
  match (Opt.get ls.ls_value).ty_node with
  | Tyapp (s,_) -> not (its_solid (restore_its s))
  | _ -> assert false

let is_fragile_projection ls =
  ls.ls_constr = 0 &&
  try let rs = restore_rs ls in
      if rs.rs_field = None then false else
      match (List.hd rs.rs_cty.cty_args).pv_ity.ity_node with
      | Ityreg {reg_its = s} | Ityapp (s,_,_) -> not (its_solid s)
      | _ -> assert false
  with Not_found -> false

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

type pin = {
  p_fields : (vsymbol * cap) Mls.t; (* temporary fields *)
  p_inv    : term;                  (* instantiated invariant *)
}

let isV = function V -> true | _ -> false

let mkP n =
  if n = 0 then V else P n

let mkC css =
  let chk _ l = List.for_all isV l in
  if Mls.for_all chk css then V else C css

let mkR pjs =
  let chk _ c = isV c in
  if Mls.for_all chk pjs then V else R pjs

let add_cap v c caps =
  if isV c then caps else Mvs.add v c caps

let new_index =
  let c = ref 0 in
  fun () -> incr c; !c

let rec get_index uf n =
  if n = 0 then 0 else
  match Mint.find_opt n uf with
  | Some n -> get_index uf n
  | None -> n

(* TODO:
  - do not collapse on Eif and Ecase in k_expr when the type is fragile

  - projection application may require committing when the argument is
    a C with unjoinable caps. We can and should detect such applications
    inside specifications and produce appropriate commits. We should also
    avoid creating such applications outside stop_split: Vc.name_regions
    should NEVER use a projection with a fragile instantiated value type.
*)

let add_var kn pins v =
  let rp = ref pins in
  let rec down ty = match ty.ty_node with
    | Tyvar _ -> V
    | Tyapp (s,tl) ->
        let s = restore_its s in
        if its_solid s then V else
        let d = find_its_defn kn s in
        let sbs = ts_match_args s.its_ts tl in
        if s.its_nonfree then if s.its_fragile then (* breakable record *)
          let bn = v.vs_name.id_string in
          let add_field (m,mv) f =
            let vf = Opt.get f.rs_field in
            let ty = Ty.ty_inst sbs vf.pv_vs.vs_ty in
            let nm = bn ^ "_" ^ f.rs_name.id_string in
            let v = create_vsymbol (id_fresh nm) ty in
            let mv = Mvs.add vf.pv_vs (t_var v) mv in
            Mls.add (ls_of_rs f) (v, down ty) m, mv in
          let pjs, mv = List.fold_left add_field
                            (Mls.empty, Mvs.empty) d.itd_fields in
          let inv = t_ty_subst sbs mv (t_and_l d.itd_invariant) in
          let pin = {p_fields = pjs; p_inv = inv} in
          let n = new_index () in
          rp := Mint.add n pin !rp;
          mkP n
        else (* unbreakable record *)
          let add_field m f =
            let vf = Opt.get f.rs_field in
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
  (* do not inline *) c, !rp

let cap_valid uf c =
  let rec down = function
    | V -> ()
    | P n -> if get_index uf n <> 0 then raise Exit
    | C css -> Mls.iter (fun _ fl -> List.iter down fl) css
    | R pjs -> Mls.iter (fun _ c -> down c) pjs in
  try down c; true with Exit -> false

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

let cap_of_term kn uf pins caps t =
  let rec unroll t = function
    | (pj,t0)::pjl ->
        let t = t_app pj [t] t0.t_ty in
        unroll (t_label_copy t0 t) pjl
    | []  -> t in
  let rec unwind t c pjl0 = match c, pjl0 with
    | _, [] -> t, c
    | V, _ -> unroll t pjl0, V
    | P n, (pj,t0)::pjl ->
        let n = get_index uf n in
        if n = 0 then unroll t pjl0, V
        else let pin = Mint.find n pins in
          let v, c = Mls.find pj pin.p_fields in
          unwind (t_label_copy t0 (t_var v)) c pjl
    | C css, (pj,t0)::pjl when Mls.cardinal css = 1 ->
        let cs, fl = Mls.choose css in
        let c = apply_projection kn pj cs fl in
        let t = t_app pj [t] t0.t_ty in
        unwind (t_label_copy t0 t) c pjl
    | C css, (pj,t0)::pjl ->
        let ty = Opt.get t.t_ty in
        let v0 = create_vsymbol (id_fresh "q") (Opt.get t0.t_ty) in
        let t0 = t_label_copy t0 (t_var v0) and p0 = pat_var v0 in
        let bb = match Mls.choose css with
          | {ls_constr = len}, _ when len > Mls.cardinal css ->
              let v = create_vsymbol (id_fresh "q") ty in
              [t_close_branch (pat_var v) (unroll (t_var v) pjl0)]
          | _ -> [] in
        let csl, sbs = match ty.ty_node with
          | Tyapp (ts,tl) ->
              find_constructors_ts kn ts, ts_match_args ts tl
          | _ -> assert false in
        let add_branch cs fl (bl, cj) =
          let fdl = List.assq cs csl in
          let mk_pat fd_ty fd = match fd with
            | Some ls when ls_equal pj ls -> p0
            | _ -> pat_wild (ty_inst sbs fd_ty) in
          let pl = List.map2 mk_pat cs.ls_args fdl in
          let c = find_projection_field pj fl fdl in
          let t0, c = unwind t0 c pjl in
          let b = t_close_branch (pat_app cs pl ty) t0 in
          b::bl, Some (Opt.fold (cap_join uf) c cj) in
        let bl, c = Mls.fold add_branch css (bb, None) in
        t_case t bl, Opt.get c
    | R pjs, (pj,t0)::pjl ->
        let c = Mls.find pj pjs in
        let t = t_app pj [t] t0.t_ty in
        unwind (t_label_copy t0 t) c pjl
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
        t_label_copy t (t_equ t1 t2), V
    | Tapp (ls,[t1]) when is_fragile_projection ls ->
        down caps ((ls,t)::pjl) t1
    | Tapp (ls,tl) when is_fragile_constructor ls ->
        begin match pjl with
        | (pj,t0)::pjl ->
            let t = apply_projection kn pj ls tl in
            down caps pjl (t_label_copy t0 t)
        | [] ->
            let tl, cl = List.split (List.map (down caps []) tl) in
            let t = t_label_copy t (t_app ls tl t.t_ty) in
            t, mkC (Mls.singleton ls cl) end
    | Tapp (ls,tl) ->
        let tl = List.map (fun t ->
          let t, c = down caps [] t in
          assert (cap_valid uf c); t) tl in
        unroll (t_label_copy t (t_app ls tl t.t_ty)) pjl, V
    | Tif (t0,t1,t2) ->
        let t0, _  = down caps [] t0 in
        let t1, c1 = down caps pjl t1 in
        let t2, c2 = down caps pjl t2 in
        t_label_copy t (t_if t0 t1 t2), cap_join uf c1 c2
    | Tlet (t0,tb) ->
        let t0, c0 = down caps [] t0 in
        let v, t1 = t_open_bound tb in
        let caps = add_cap v c0 caps in
        let t1, c1 = down caps pjl t1 in
        t_label_copy t (t_let_close v t0 t1), c1
    | Tcase (t0,bl) ->
        let t0, c0 = down caps [] t0 in
        let add_branch b (bl, cj) =
          let p, t1 = t_open_branch b in
          let caps = add_pat uf caps c0 p in
          let t1, c = down caps pjl t1 in
          let b = t_close_branch p t1 in
          b::bl, Some (Opt.fold (cap_join uf) c cj) in
        let bl, c = List.fold_right add_branch bl ([], None) in
        t_label_copy t (t_case t0 bl), Opt.get c
    | Teps tb ->
        let v, f = t_open_bound tb in
        let f, _ = down caps [] f in
        unroll (t_label_copy t (t_eps_close v f)) pjl, V
    | Tquant (q,tq) ->
        let vl, tt, t0 = t_open_quant tq in
        let down t = fst (down caps [] t) in
        let tt = List.map (List.map down) tt in
        let tq = t_close_quant vl tt (down t0) in
        t_label_copy t (t_quant q tq), V
    | Tbinop (op,f1,f2) ->
        let f1, _ = down caps [] f1 in
        let f2, _ = down caps [] f2 in
        t_label_copy t (t_binary op f1 f2), V
    | Tnot f ->
        let f, _ = down caps [] f in
        t_label_copy t (t_not f), V
    | Ttrue | Tfalse ->
        t, V
  in
  down caps [] t

let find_term_fields kn cs t =
  let fdl = find_constructor_fields kn cs in
  let sbs = oty_match Mtv.empty cs.ls_value t.t_ty in
  let add_pat ty (pl,pll) =
    let pw = pat_wild (ty_inst sbs ty) in
    let pv = pat_var (create_vsymbol (id_fresh "v") pw.pat_ty) in
    pw :: pl, (pv :: pl) :: List.map (fun pl -> pw :: pl) pll in
  let _, pll = List.fold_right add_pat cs.ls_args ([],[]) in
  let conv t pl = function
    | Some pj -> t_app_infer pj [t]
    | None ->
        let p = pat_app cs pl (t_type t) in
        let v = Svs.choose p.pat_vars in
        t_case_close t [p, t_var v] in
  List.map2 (conv t) pll fdl

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
        Mls.fold add p.p_fields (fl,uf)
    | C css when (fst (Mls.choose css)).ls_constr = 1 ->
        (* css cannot be empty and has at most one elt *)
        let cs, cl = Mls.choose css in
        let tl = find_term_fields kn cs t in
        let add t c (fl, uf) = commit t c fl uf in
        List.fold_right2 add tl cl (fl, uf)
    | C _css ->
        assert false (* TODO *)
    | R pjs ->
        let add pj c (fl,uf) =
          commit (t_app_infer pj [t]) c fl uf in
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
        Mls.fold2_inter add p1.p_fields p2.p_fields (fl,uf)
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

let rec track kn uf pins caps pos f = match f.t_node with
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
      Mls.iter check p.p_fields;
      p.p_inv, uf
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
      t_and_l (Mls.fold add p.p_fields []), uf
  | Tapp (ls,[t1;t2]) when not pos && ls_equal ls ps_equ ->
      let t1, c1 = cap_of_term kn uf pins caps t1 in
      let t2, c2 = cap_of_term kn uf pins caps t2 in
      let f = t_label_copy f (t_equ t1 t2) in
      cap_equality kn uf pins f t1 c1 t2 c2
  | _ when Slab.mem stop_split f.t_label ->
      fst (cap_of_term kn uf pins caps f), uf
  | Tapp _ ->
      fst (cap_of_term kn uf pins caps f), uf
  | Tif (f0,f1,f2) ->
      let f0, _ = cap_of_term kn uf pins caps f0 in
      let f1, uf1 = track kn uf pins caps pos f1 in
      let f2, uf2 = track kn uf pins caps pos f2 in
      t_label_copy f (t_if f0 f1 f2), uf_inter uf1 uf2
  | Tlet (t0,fb) ->
      let t0, c0 =  cap_of_term kn uf pins caps t0 in
      let v, f1 = t_open_bound fb in
      let caps = add_cap v c0 caps in
      let f1, uf = track kn uf pins caps pos f1 in
      t_label_copy f (t_let_close v t0 f1), uf
  | Tcase (t0,bl) ->
      let t0, c0 = cap_of_term kn uf pins caps t0 in
      let add_branch b (bl, ufj) =
        let p, f1 = t_open_branch b in
        let caps = add_pat uf caps c0 p in
        let f1, uf1 = track kn uf pins caps pos f1 in
        let b = t_close_branch p f1 in
        b::bl, Some (Opt.fold uf_inter uf1 ufj) in
      let bl, uf = List.fold_right add_branch bl ([], None) in
      t_label_copy f (t_case t0 bl), Opt.get uf
  | Tquant (q,fq) ->
      let vl, tt, f0 = t_open_quant fq in
      let down t = fst (cap_of_term kn uf pins caps t) in
      let tt = List.map (List.map down) tt in
      let valid = match q with
        | Tforall -> not pos
        | Texists -> pos in
      let caps, pins =
        if valid then caps, pins else
        let add (caps, pins) v =
          let c, pins = add_var kn pins v in
          add_cap v c caps, pins in
        List.fold_left add (caps, pins) vl in
      let f0, uf = track kn uf pins caps pos f0 in
      let f0 = t_quant q (t_close_quant vl tt f0) in
      t_label_copy f f0, uf
  | Tbinop (Tand,f1,f2) ->
      let f1, uf1 = track kn uf  pins caps pos f1 in
      let f2, uf2 = track kn uf1 pins caps pos f2 in
      t_label_copy f (t_and f1 f2), uf2
  | Tbinop (Timplies,f1,f2) ->
      let f1, uf1 = track kn uf  pins caps (not pos) f1 in
      let f2, _   = track kn uf1 pins caps pos f2 in
      t_label_copy f (t_implies f1 f2), uf
  | Tbinop (Tor,f1,f2) ->
      let f1, uf1 = track kn uf pins caps pos f1 in
      let f2, uf2 = track kn uf pins caps pos f2 in
      t_label_copy f (t_or f1 f2), uf_inter uf1 uf2
  | Tbinop (Tiff,_,_) ->
      fst (cap_of_term kn uf pins caps f), uf
  | Tnot f1 ->
      let f1, _ = track kn uf pins caps (not pos) f1 in
      t_label_copy f (t_not f1), uf
  | Ttrue | Tfalse ->
      f, uf

let track kn f =
  fst (track kn Mint.empty Mint.empty Mvs.empty true f)

(* Part II - EvalMatch simplification *)

(* we destruct tuples, units, and singleton records *)
let destructible kn ty =
  match find_constructors kn ty with
  | [ls,_] when is_fs_tuple ls -> Some ls
  | [{ls_args = [_]} as ls, _] -> Some ls
  | [{ls_args = []}  as ls, _] -> Some ls
  | _ -> None

(* we inline projections of destructed types *)
let find_inlineable kn ls = match ls.ls_args with
  | [arg] when destructible kn arg <> None ->
      begin match find_logic_definition kn ls with
      | Some def ->
          let res = open_ls_defn def in
          begin match (snd res).t_node with
          | Tvar _ | Tconst _
          | Tapp (_, [{t_node = Tvar _}]) -> Some res
          | Tcase ({t_node = Tvar _}, [bt]) ->
              begin match t_open_branch bt with
              | _, {t_node = Tvar _} -> Some res
              | _ -> None end
          | _ -> None end
      | _ -> None end
  | _ -> None

let unfold_inlineable kn ls tl ty = match find_inlineable kn ls with
  | Some (vl, e) ->
      let mt = List.fold_left2 (fun mt x y ->
        ty_match mt x.vs_ty (t_type y)) Mtv.empty vl tl in
      let mv = List.fold_right2 Mvs.add vl tl Mvs.empty in
      Some (t_ty_subst (oty_match mt e.t_ty ty) mv e)
  | None -> None

let rec add_quant kn (vl,tl,f) ({vs_ty = ty} as v) =
  match destructible kn ty with
  | Some ls ->
      let s = ty_match Mtv.empty (Opt.get ls.ls_value) ty in
      let mk_v ty = create_vsymbol (id_clone v.vs_name) (ty_inst s ty) in
      let nvl = List.map mk_v ls.ls_args in
      let t = fs_app ls (List.map t_var nvl) ty in
      let f = t_let_close_simp v t f in
      let tl = tr_map (t_subst_single v t) tl in
      List.fold_left (add_quant kn) (vl,tl,f) nvl
  | None ->
      (v::vl, tl, f)

let let_map fn env t1 tb =
  let x,t2,close = t_open_bound_cb tb in
  let t2 = fn (Mvs.add x t1 env) t2 in
  (* TODO/FIXME? convert (let x = if f then True else False in h)
     into (forall x. (x = True <-> f) -> h) ? *)
  t_let_simp t1 (close x t2)

let branch_map fn env t1 bl =
  let mk_b b =
    let p,t2,close = t_open_branch_cb b in close p (fn env t2) in
  t_case t1 (List.map mk_b bl)

let rec dive_to_constructor fn env t =
  let dive env t = dive_to_constructor fn env t in
  t_label_copy t (match t.t_node with
    | Tvar x -> dive env (Mvs.find_exn Exit x env)
    | Tlet (t1,tb) -> let_map dive env t1 tb
    | Tcase (t1,bl) -> branch_map dive env t1 bl
    | Tif (f,t1,t2) -> t_if_simp f (dive env t1) (dive env t2)
    | Tapp (ls,tl) when ls.ls_constr > 0 -> fn env t ls tl
    | _ -> raise Exit)

let rec cs_equ env t1 t2 =
  if t_equal t1 t2 then t_true else
  let right cs1 tl1 env _t2 cs2 tl2 =
    if not (ls_equal cs1 cs2) then t_false else
    t_and_simp_l (List.map2 (cs_equ env) tl1 tl2) in
  let left t2 env _t1 cs1 tl1 =
    dive_to_constructor (right cs1 tl1) env t2 in
  try dive_to_constructor (left t2) env t1
  with Exit -> t_equ t1 t2

let flat_case t bl =
  let mk_b b = let p,t = t_open_branch b in [p],t in
  let mk_case = t_case_close and mk_let = t_let_close_simp in
  Pattern.compile_bare ~mk_case ~mk_let [t] (List.map mk_b bl)

let rec eval_match kn stop env t =
  let stop = stop || Slab.mem Term.stop_split t.t_label in
  let eval env t = eval_match kn stop env t in
  t_label_copy t (match t.t_node with
    | Tapp (ls, [t1;t2]) when ls_equal ls ps_equ ->
        cs_equ env (eval env t1) (eval env t2)
    | Tapp (ls, [t1]) when is_projection ls ->
        let t1 = eval env t1 in
        let fn _env _t2 cs tl = apply_projection kn ls cs tl in
        begin try dive_to_constructor fn env t1
        with Exit -> t_app ls [t1] t.t_ty end
    | Tapp (ls, tl) ->
        begin match unfold_inlineable kn ls tl t.t_ty with
        | Some t -> eval env t
        | None -> t_map (eval env) t
        end
    | Tlet (t1, tb2) ->
        let t1 = eval env t1 in
        let_map eval env t1 tb2
    | Tcase (t1, bl1) ->
        let t1 = eval env t1 in
        let fn env t2 _cs _tl =
          eval env (Loc.try2 ?loc:t.t_loc flat_case t2 bl1) in
        begin try dive_to_constructor fn env t1
        with Exit -> branch_map eval env t1 bl1 end
    | Tquant (q, qf) ->
        let vl,tl,f,close = t_open_quant_cb qf in
        let vl,tl,f = if stop then List.rev vl,tl,f else
          List.fold_left (add_quant kn) ([],tl,f) vl in
        t_quant_simp q (close (List.rev vl) tl (eval env f))
    | _ ->
        t_map (eval env) t)

let eval_match kn t = eval_match kn false Mvs.empty t
