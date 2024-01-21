open Why3
open Wstdlib
open Ident
open Ty
open Term
open Coma_syntax

module Hsym = MakeMSHW (struct
  type t = hsymbol
  let tag hs = hs.hs_name.id_tag
end)

module Shs = Hsym.S
module Mhs = Hsym.M

(*
module Hhs = Hsym.H
module Whs = Hsym.W

let hs_equal : hsymbol -> hsymbol -> bool = (==)
let hs_hash hs = id_hash hs.hs_name
let hs_compare hs1 hs2 = id_compare hs1.hs_name hs2.hs_name
*)

let case_split = create_attribute "case_split"
let add_case t = t_attr_add case_split t

let debug_slow = Debug.register_info_flag "coma_no_merge"
  ~desc:"Disable@ subgoal@ factorization."

exception BadUndef of hsymbol

let is_true f = match f.t_node with
  | Ttrue -> true | _ -> false

let t_and_simp f1 f2 = match f1.t_node, f2.t_node with
  | _, Ttrue | Tfalse, _ -> t_attr_remove asym_split f1
  | Ttrue, _ | _, Tfalse -> f2
  | _, _ -> t_and f1 f2

let t_and_asym_simp f1 f2 = t_and_simp (t_attr_add asym_split f1) f2

let t_implies_simp f1 f2 = match f1.t_node, f2.t_node with
  | Ttrue, _  | _, Ttrue  -> f2
  | Tfalse, _ | _, Tfalse -> t_not_simp f1
  | _, _ -> t_implies f1 f2

let t_if_simp f1 f2 f3 = match f1.t_node, f2.t_node, f3.t_node with
  | Ttrue, _, _  -> f2
  | Tfalse, _, _ -> f3
  | _, Ttrue, _  -> t_implies_simp (t_not_simp f1) f3
  | _, Tfalse, _ -> t_and_asym_simp (t_not_simp f1) f3
  | _, _, Ttrue  -> t_implies_simp f1 f2
  | _, _, Tfalse -> t_and_asym_simp f1 f2
  | _, _, _ -> t_if f1 f2 f3

let rec t_equ_simp t1 t2 = match t1.t_node, t2.t_node with
  | Tvar v1, Tvar v2 when vs_equal v1 v2 -> t_true
  | Tapp (s1,[]), Tapp (s2,[]) when ls_equal s1 s2 -> t_true
  | Tapp (s1,_), Tapp (s2,_) when s1.ls_constr > 0 && s2.ls_constr > 0
                                  && not (ls_equal s1 s2) -> t_false
  | Tconst c1, Tconst c2 when Constant.compare_const c1 c2 = 0 -> t_true
  | Tif (c,t1,e1), _ -> t_if_simp c (t_equ_simp t1 t2) (t_equ_simp e1 t2)
  | _, Tif (c,t2,e2) -> t_if_simp c (t_equ_simp t1 t2) (t_equ_simp t1 e2)
  | _, _ -> t_equ t1 t2

let rec t_simp_equ f = match f.t_node with
  | Tapp (s,[t1;t2]) when ls_equal s ps_equ ->
      t_attr_copy f (t_equ_simp t1 t2)
  | Tnot g ->
      t_attr_copy f (t_not_simp (t_simp_equ g))
  | Tbinop (Tand,g,h) ->
      t_attr_copy f (t_and_simp (t_simp_equ g) (t_simp_equ h))
  | Tbinop (Tor,g,h) ->
      t_attr_copy f (t_or_simp (t_simp_equ g) (t_simp_equ h))
  | Tbinop (Timplies,g,h) ->
      t_attr_copy f (t_implies_simp (t_simp_equ g) (t_simp_equ h))
  | Tquant (q,b) -> let vl,tl,g = t_open_quant b in
      t_attr_copy f (t_quant_close_simp q vl tl (t_simp_equ g))
  | _ -> t_map t_simp_equ f

let rec t_neg f =
  if Sattr.mem stop_split f.t_attrs then f
  else t_attr_copy f (match f.t_node with
    | Tnot g -> t_attr_copy f g
    | Tbinop (Tand,g,h) -> t_or (t_neg g) (t_neg h)
    | Tbinop (Tor,g,h) -> t_and (t_neg g) (t_neg h)
    | Tbinop (Timplies,g,h) -> t_and g (t_neg h)
    | Tquant (q,b) ->
        let q = if q = Texists then
                Tforall else Texists in
        let vl,tl,g = t_open_quant b in
        t_quant_close q vl tl (t_neg g)
    | _ -> f)

let t_level vsl t =
  Mvs.fold (fun v _ m -> max m (Mvs.find v vsl)) (t_vars t) 0

let sbs_merge vsl m1 m2 = Mvs.union (fun _ t1 t2 ->
  Some (if t_level vsl t2 < t_level vsl t1 then t2 else t1)) m1 m2

let add_vl vl t m = List.fold_left (fun m v -> Mvs.add v t m) m vl

let rec propagate lvl vsl pvs nvs f = match f.t_node with
  | Tapp (s,[{t_node = Tvar v};t])
    when ls_equal s ps_equ && Svs.mem v pvs &&
         Mvs.find v vsl > t_level vsl t ->
      f, Mvs.singleton v t
  | Tapp (s,[t;{t_node = Tvar v}])
    when ls_equal s ps_equ && Svs.mem v pvs &&
         Mvs.find v vsl > t_level vsl t ->
      f, Mvs.singleton v t
  | Tnot g ->
      let g, sbs = propagate lvl vsl nvs pvs g in
      t_attr_copy f (t_not g), sbs
  | Tbinop (Tand,g,h) ->
      let g, sbg = propagate lvl vsl pvs Svs.empty g in
      let h, sbh = propagate lvl vsl pvs Svs.empty h in
      t_attr_copy f (t_and g h), sbs_merge vsl sbg sbh
  | Tbinop (Tor,g,h) ->
      let g, sbg = propagate lvl vsl Svs.empty nvs g in
      let h, sbh = propagate lvl vsl Svs.empty nvs h in
      t_attr_copy f (t_or g h), sbs_merge vsl sbg sbh
  | Tbinop (Timplies,g,h) ->
      let g, sbg = propagate lvl vsl nvs Svs.empty g in
      let h, sbh = propagate lvl vsl Svs.empty nvs h in
      t_attr_copy f (t_implies g h), sbs_merge vsl sbg sbh
  | Tquant (q,b) ->
      let vl,tl,g = t_open_quant b in
      let vsl = add_vl vl lvl vsl in
      let avs = add_vl vl () Svs.empty in
      let pvs = if q = Texists then Svs.union pvs avs else pvs in
      let nvs = if q = Texists then nvs else Svs.union nvs avs in
      let g, sbs = propagate (succ lvl) vsl pvs nvs g in
      let inst = t_subst (Mvs.set_inter sbs avs) in
      let g = inst g and tl = List.map (List.map inst) tl in
      t_attr_copy f (t_quant_close q vl tl g), Mvs.set_diff sbs avs
  | _ ->
      f, Mvs.empty

let vc_simp f =
  t_simp_equ f
  |> propagate 0 Mvs.empty Svs.empty Svs.empty |> fst
  |> t_simp_equ

let spec_simp vl f =
  t_simp_equ f
  |> propagate 1 (add_vl vl 0 Mvs.empty) Svs.empty Svs.empty |> fst
  |> t_simp_equ

type wpsp = {
  wp: term;
  sp: term Mhs.t;
}

let w_true = { wp = t_true; sp = Mhs.empty }

let sp_or _ sp1 sp2 = Some (
  match sp1.t_node, sp2.t_node with
  | Ttrue, _ | _, Tfalse -> sp1
  | _, Ttrue | Tfalse, _ -> sp2
  | _, _ -> add_case (t_or sp1 sp2))

let w_and w1 w2 = {
  wp = t_and_simp w1.wp w2.wp;
  sp = Mhs.union sp_or w1.sp w2.sp
}

let rec w_and_l = function
  | [] -> w_true | [w] -> w
  | w::wl -> w_and w (w_and_l wl)

let w_and_asym f w = {
  wp = t_and_asym_simp f w.wp;
  sp = Mhs.map (t_and_simp f) w.sp;
}

let w_implies f w = {
  wp = t_implies_simp f w.wp;
  sp = Mhs.map (t_and_simp f) w.sp;
}

let w_forall vl w = {
  wp = t_forall_close_simp vl [] w.wp;
  sp = Mhs.map (t_exists_close_simp vl []) w.sp
}

let w_subst s w = {
  wp = t_subst s w.wp;
  sp = Mhs.map (t_subst s) w.sp
}

type context = {
  c_tv : ty Mtv.t;
  c_vs : term Mvs.t;
  c_hs : handler Mhs.t;
  c_lc : Shs.t;
  c_gl : bool;
}

and handler = bool -> context -> closure
and closure = binding list -> wpsp

and binding =
  | Bt of ty
  | Bv of term
  | Br of term * vsymbol
  | Bc of context * (context -> closure)

let c_empty = {
  c_tv = Mtv.empty;
  c_vs = Mvs.empty;
  c_hs = Mhs.empty;
  c_lc = Shs.empty;
  c_gl = true;
}

let c_find_tv c u = Mtv.find u c.c_tv
let c_find_vs c v = Mvs.find v c.c_vs
let c_find_hs c h = Mhs.find h c.c_hs

let c_inst_ty c t = ty_inst c.c_tv t
let c_inst_t  c s = t_ty_subst c.c_tv c.c_vs s

let c_clone_tv u = create_tvsymbol (id_clone u.tv_name)
let c_clone_vs c v =
  create_vsymbol (id_clone v.vs_name) (c_inst_ty c v.vs_ty)

let c_add_tv c u t = { c with c_tv = Mtv.add u t c.c_tv }
let c_add_vs c v s = { c with c_vs = Mvs.add v s c.c_vs }
let c_add_hs c h k = { c with c_hs = Mhs.add h k c.c_hs ;
  c_lc = if c.c_gl then Shs.empty else Shs.add h c.c_lc }

let callsym sf h c bl =
  c_find_hs c h (sf && (c.c_gl || Shs.mem h c.c_lc)) c bl

let nasty check pl = List.exists (function
  | Pv _ | Pr _ -> false | Pt _ -> true
  | Pc (_,_,pl) -> check pl) pl

let unmergeable = nasty Util.ttrue
let unspeccable = nasty unmergeable

let rec consume merge c pl bl =
  let eat (c,zl,hl,mr) p b = match p,b with
    | Pt u, Bt t -> c_add_tv c u t, zl, hl, mr
    | Pv v, Bv s -> c_add_vs c v s, zl, hl, mr
    | Pr p, Br (s,r) -> c_add_vs c p s, zl, hl, Mvs.add p r mr
    | Pc (h,wr,pl), Bc (cc,kk) ->
        let link up p = Mvs.add (Mvs.find_def p p mr) p up in
        let up = List.fold_left link Mvs.empty wr in
        let kk sf c bl = (* handler of closure *)
          if sf && Mvs.is_empty up then kk cc bl else
          let lc = if sf then cc.c_lc else Shs.empty in
          let iv = Mvs.set_union (Mvs.map (c_find_vs c) up) cc.c_vs in
          kk {cc with c_vs = iv; c_lc = lc; c_gl = sf && cc.c_gl} bl in
        let kk,zl,hl = factorize merge c zl hl h wr pl kk in
        c_add_hs c h kk, zl, hl, mr
    | _ -> assert false in
  let c,zl,hl,_ = List.fold_left2 eat (c,[],[],Mvs.empty) pl bl in
  c, discharge zl hl

and factorize merge c zl0 hl h wr pl kk =
  if Debug.test_flag debug_slow || unmergeable pl then kk,zl0,hl else
  let dup (zl,zv) v = let z = c_clone_vs c v in z::zl, Mvs.add z v zv in
  let zl, zv = List.fold_left (fun a -> function Pt _ | Pc _ -> assert false
    | Pv v | Pr v -> dup a v) (List.fold_left dup (zl0, Mvs.empty) wr) pl in
  let zm = Mvs.fold (fun z v m -> Mvs.add v (t_var z) m) zv Mvs.empty in
  let zc = { c_empty with c_vs = zm } in
  let bl = List.map (function Pt _ | Pc _ -> assert false
    | Pr v -> Br (Mvs.find v zm,v) | Pv v -> Bv (Mvs.find v zm)) pl in
  match kk true zc bl with exception BadUndef _ -> kk,zl0,hl | zw ->
  if not merge || is_true zw.wp then
    let zk sf c bl = if not sf then w_true else
      if Mvs.is_empty zv then zw else
      let c,_ = consume false c pl bl in
      w_subst (Mvs.map (c_find_vs c) zv) zw in
    zk, zl0, hl
  else
    let hc = create_hsymbol (id_clone h.hs_name) in
    let zk sf c bl = if not sf then w_true else
      let c,_ = consume false c pl bl in
      let link v z f = t_and_simp (t_equ z (c_find_vs c v)) f in
      let sp = Mhs.singleton hc (Mvs.fold_right link zm t_true) in
      { wp = t_true; sp = sp } in
    zk, zl, (hc,zw)::hl

and discharge zl hl ws =
  if hl = [] then ws else
  let wl,sp = List.fold_left (fun (wl,sp) (hc,zw) ->
    w_implies (Mhs.find_def t_false hc sp) zw :: wl,
    Mhs.remove hc sp) ([], ws.sp) hl in
  let wl = { ws with sp = sp } :: wl in
  w_forall (List.rev zl) (w_and_l wl)

let rec havoc c wr pl =
  let on_write (c,vl) v =
    let u = c_clone_vs c v in
    c_add_vs c v (t_var u), u::vl in
  let on_param (c,vl as acc) = function
    | Pc (h,_,pl) -> c_add_hs c h (undef h c pl), vl
    | Pt v -> c_add_tv c v (ty_var (c_clone_tv v)), vl
    | Pv v | Pr v -> on_write acc v in
  let c_vl = List.fold_left on_write (c,[]) wr in
  let c,vl = List.fold_left on_param (c_vl) pl in
  c, List.rev vl

and undef h c pl sf _ bl =
  if sf && c.c_gl then raise (BadUndef h);
  let lc = if sf then c.c_lc else Shs.empty in
  let c = { c with c_lc = lc; c_gl = false } in
  let c,_ = consume false c pl bl in
  let expand h wr pl =
    let h = c_find_hs c h in
    let c, vl = havoc c wr pl in
    let mkb = function
      | Pt u -> Bt (c_find_tv c u)
      | Pv v -> Bv (c_find_vs c v)
      | Pr r -> Br (c_find_vs c r, r)
      | Pc (g,_,_) -> Bc (c, callsym true g) in
    w_forall vl (h true c (List.map mkb pl)) in
  w_and_l (List.filter_map (function
    | Pc (h,wr,pl) -> Some (expand h wr pl)
    | Pt _ | Pv _ | Pr _ -> None) pl)

let rec vc pp dd e c bl =
  if ((not c.c_gl && Shs.is_empty c.c_lc) ||
    not (pp || dd)) && bl = [] then w_true else
  match e with
  | Esym h ->
      callsym pp h c bl
  | Eapp (e, a) ->
      let b = match a with
        | At t -> Bt (c_inst_ty c t)
        | Av s -> Bv (c_inst_t c s)
        | Ar r -> Br (c_find_vs c r, r)
        | Ac d -> Bc (c, vc pp dd d) in
      vc pp dd e c (b::bl)
  | Elam (pl,e) ->
      let c, close = consume true c pl bl in
      let lc = List.fold_left (fun s -> function
        | Pt _ | Pv _ | Pr _ -> s
        | Pc (h,_,_) -> Shs.add h s) Shs.empty pl in
      let cc = { c with c_lc = lc; c_gl = false } in
      let ww = vc (not pp) (not dd) e cc [] in
      close (w_and (vc pp dd e c []) ww)
  | Edef (e,flat,dfl) -> assert (bl = []);
      (* recursive definitions are not mergeable *)
      let c, close, wl = vc_defn pp c flat true dfl in
      w_and_l (close (vc pp dd e c []) :: wl)
  | Eset (e,vtl) -> assert (bl = []);
      let add cc (v,s) = c_add_vs cc v (c_inst_t c s) in
      vc pp dd e (List.fold_left add c vtl) bl
  | Elet (e,vtl) -> assert (bl = []);
      let add cc (v,s,_) = c_add_vs cc v (c_inst_t c s) in
      vc pp dd e (List.fold_left add c vtl) bl
  | Ecut (f,e) -> assert (bl = []);
      let f = t_attr_add stop_split f in
      (if pp && c.c_gl then w_and_asym else w_implies)
        (c_inst_t c f) (vc pp dd e c bl)
  | Ebox e -> assert (bl = []); vc dd dd e c bl
  | Ewox e -> assert (bl = []); vc pp pp e c bl
  | Eany   -> assert (bl = []); w_true

and vc_defn pp c flat merge dfl =
  let pl = List.map (fun (h,w,pl,_) -> Pc (h,w,pl)) dfl in
  let cc = if flat then c else fst (havoc c [] pl) in
  let bl = List.map (fun (_,_,pl,d) -> Bc (cc, fun c bl ->
    let c, close = consume true c pl bl in
    close (vc true false d c []))) dfl in
  let c, close = consume (flat && merge) cc pl bl in
  c, close, List.map (fun (_,w,pl,d) ->
    let c, vl = havoc (if flat then cc else c) w pl in
    w_forall vl (vc false pp d c [])) dfl

let vc_expr c e = vc_simp (vc true true e c []).wp

let vc_defn c flat dfl =
  (* top-level definitions are not mergeable *)
  let c,_,wl = vc_defn true c flat false dfl in
  c, List.map2 (fun (h,_,_,_) w -> h, vc_simp w.wp) dfl wl

let extspec_attr = create_attribute "coma:extspec"
let hs_extspec h = Sattr.mem extspec_attr h.hs_name.id_attrs

let vc_spec c ({hs_name = {id_string = n}} as h) w pl =
  if not (hs_extspec h) || unspeccable pl then [] else
  let id_pre = id_fresh (n ^ "'pre") in
  let on_write (ul,c) v =
    let u = c_clone_vs c v in
    u::ul, c_add_vs c v (t_var u) in
  let ul, c = List.fold_left on_write ([],c) w in
  let hr = Hvs.create 7 in
  let on_param (ul,bl,outs) = function
    | Pt _ -> assert false
    | Pv v ->
        let u = c_clone_vs c v in
        let b = Bv (t_var u) in
        u::ul, b::bl, List.map (fun (id,ul,bl) -> id, u::ul, b::bl) outs
    | Pr v ->
        let u = c_clone_vs c v in
        let b = Br (t_var u, u) in Hvs.add hr v u;
        u::ul, b::bl, List.map (fun (id,ul,bl) -> id, u::ul, b::bl) outs
    | Pc ({hs_name = {id_string = s}},w,pl) ->
        let b = Bc (c, fun _ _ -> w_true) in
        let add_var (ul,fl) v =
          let u = c_clone_vs c v in
          u::ul, t_equ (t_var u) (t_var v) :: fl in
        let add_write acc v =
          add_var acc (Hvs.find_def hr v v) in
        let add_param acc = function
          | Pt _ | Pc _ -> assert false
          | Pv v | Pr v -> add_var acc v in
        let zl,fl = List.fold_left add_write (ul,[]) w in
        let zl,fl = List.fold_left add_param (zl,fl) pl in
        let f = t_not_simp (t_and_l (List.rev fl)) in
        let kk c bl =
          let c,_ = consume false c pl bl in
          { wp = c_inst_t c f; sp = Mhs.empty } in
        let oo = id_fresh (n ^ "'post'" ^ s), zl, Bc (c, kk) :: bl in
        ul, b::bl, oo :: List.map (fun (id,ul,bl) -> id, ul, b::bl) outs
  in
  let ul,bl,outs = List.fold_left on_param (ul,[],[]) pl in
  let get pp ul bl = spec_simp ul (callsym pp h c (List.rev bl)).wp in
  (id_pre, List.rev ul, get true ul bl) :: List.rev_map (fun (id,ul,bl) ->
       id, List.rev ul, t_neg (get false ul bl)) outs

let () = Exn_printer.register (fun fmt -> function
  | BadUndef h -> Format.fprintf fmt
      "Handler `%a' is used in an illegal position" Coma_syntax.PP.pp_hs h
  | exn -> raise exn)
