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

(*
let t_and_simp = t_and
let t_and_asym_simp = t_and_asym
let t_implies_simp = t_implies
let t_forall_close_simp = t_forall_close
*)

type wpsp = {
  wp: term;
  sp: term Mhs.t;
}

let w_true  = { wp = t_true;  sp = Mhs.empty }
let w_false = { wp = t_false; sp = Mhs.empty }

let w_and w1 w2 = {
  wp = t_and_simp w1.wp w2.wp;
  sp = Mhs.union (fun _ f1 f2 -> Some (t_or_simp f1 f2)) w1.sp w2.sp
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

type context = {
  c_tv : ty Mtv.t;
  c_vs : term Mvs.t;
  c_hs : closure Mhs.t;
  c_lc : Shs.t;
  c_gl : bool;
}

and closure = bool -> callable

and callable = context -> binding list -> wpsp

and binding =
  | Bt of ty
  | Bv of term
  | Br of term * vsymbol
  | Bc of context * callable * bool

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

let rec consume c pl bl =
  let eat (c,zl,hl,mr) p b = match p,b with
    | Pt u, Bt t -> c_add_tv c u t, zl, hl, mr
    | Pv v, Bv s -> c_add_vs c v s, zl, hl, mr
    | Pr p, Br (s,r) -> c_add_vs c p s, zl, hl, Mvs.add p r mr
    | Pc ({hs_name = {id_string = s}} as h,wr,pl), Bc (cc,kk,sub) ->
        let link up p = Mvs.add (Mvs.find_def p p mr) p up in
        let up = List.fold_left link Mvs.empty wr in
        let kk sf c bl = (* closure of callable *)
          if sf && Mvs.is_empty up then kk cc bl else
          let lc = if sf then cc.c_lc else Shs.empty in
          let iv = Mvs.set_union (Mvs.map (c_find_vs c) up) cc.c_vs in
          kk {cc with c_vs = iv; c_lc = lc; c_gl = sf && cc.c_gl} bl in
        if sub && List.for_all (function Pv _ | Pr _ -> true
          | Pt _ | Pc _ -> false) pl && (s <> "" && s.[0] = '_')
        then let kk,zl,hl = factorize c zl hl h wr pl kk in
             c_add_hs c h kk, zl, hl, mr
        else c_add_hs c h kk, zl, hl, mr
    | _ -> assert false in
  let c,zl,hl,_ = List.fold_left2 eat (c,[],[],Mvs.empty) pl bl in
  c, discharge zl hl

and factorize c zl hl h wr pl kk =
  let hc = create_hsymbol (id_clone h.hs_name) in
  let dup (l,m) v = let z = c_clone_vs c v in z::l, Mvs.add v (t_var z) m in
  let zl,zm = List.fold_left (fun a -> function Pt _ | Pc _ -> assert false
    | Pv v | Pr v -> dup a v) (List.fold_left dup (zl, Mvs.empty) wr) pl in
  let bl = List.map (function Pt _ | Pc _ -> assert false
    | Pr v -> Br (Mvs.find v zm,v) | Pv v -> Bv (Mvs.find v zm)) pl in
  let zk sf c bl = if not sf then w_true else
    let c,_ = consume c pl bl (* no handlers in pl *) in
    let link v z f = t_and_simp (t_equ z (c_find_vs c v)) f in
    let sp = Mhs.singleton hc (Mvs.fold_right link zm t_true) in
    { wp = t_true; sp = sp } in
  zk, zl, (hc,kk,zm,bl)::hl

and discharge zl hl w =
  if hl = [] then w else
  let wl = List.rev_map (fun (h,kk,zm,bl) ->
    let sp = Mhs.find_def t_false h w.sp in
    (* if is_false sp then w_true else *)
    let cc = { c_empty with c_vs = zm } in
    w_implies sp (kk true cc bl)) hl in
  let drop s (h,_,_,_) = Mhs.remove h s in
  let sp = List.fold_left drop w.sp hl in
  let wl = { w with sp = sp } :: wl in
  w_forall (List.rev zl) (w_and_l wl)

let rec havoc c wr pl =
  let on_write (c,vl) v =
    let u = c_clone_vs c v in
    c_add_vs c v (t_var u), u::vl in
  let on_param (c,vl as acc) = function
    | Pc (h,_,pl) -> c_add_hs c h (undef c pl), vl
    | Pt v -> c_add_tv c v (ty_var (c_clone_tv v)), vl
    | Pv v | Pr v -> on_write acc v in
  let c_vl = List.fold_left on_write (c,[]) wr in
  let c,vl = List.fold_left on_param (c_vl) pl in
  c, List.rev vl

and undef c pl sf _ bl =
  let gl = sf && c.c_gl in
  (* if gl then w_false else *)
  w_and (if gl then w_false else w_true) (
  let lc = if sf then c.c_lc else Shs.empty in
  let c = { c with c_lc = lc; c_gl = gl } in
  (* TODO: suppress factorization *)
  let c, close = consume c pl bl in
  let expand h wr pl =
    let h = c_find_hs c h in
    let c, vl = havoc c wr pl in
    let mkb = function
      | Pt u -> Bt (c_find_tv c u)
      | Pv v -> Bv (c_find_vs c v)
      | Pr r -> Br (c_find_vs c r, r)
      | Pc (g,_,_) -> Bc (c, callsym true g, false) in
    w_forall vl (h true c (List.map mkb pl)) in
  close (w_and_l (List.filter_map (function
    | Pc (h,wr,pl) -> Some (expand h wr pl)
    | Pt _ | Pv _ | Pr _ -> None) pl)))

let substantial pp dd e c =
  let rec check = function
    | Elam (_,e) | Eset (e,_) | Ecut (_,e) -> check e
    | Edef (e,_,_) when not pp -> check e
    | Ebox _ when not dd -> false
    | Ewox _ when not pp -> false
    | Eany -> false
    | _ -> pp || dd in
  (c.c_gl || not (Shs.is_empty c.c_lc)) && check e

let rec vc pp dd e c bl = match e with
  | Esym h ->
      callsym pp h c bl
  | Eapp (e, a) ->
      let b = match a with
        | At t -> Bt (c_inst_ty c t)
        | Av s -> Bv (c_inst_t c s)
        | Ar r -> Br (c_find_vs c r, r)
        | Ac d -> Bc (c, vc pp dd d, substantial pp dd d c) in
      vc pp dd e c (b::bl)
  | Elam (pl,e) ->
      let c, close = consume c pl bl in
      let lc = List.fold_left (fun s -> function
        | Pt _ | Pv _ | Pr _ -> s
        | Pc (h,_,_) -> Shs.add h s) Shs.empty pl in
      let cc = { c with c_lc = lc; c_gl = false } in
      close (w_and (vc pp dd e c []) (vc (not pp) (not dd) e cc []))
  | Edef (e,flat,dfl) -> assert (bl = []);
      let pl = List.map (fun (h,w,pl,_) -> Pc (h,w,pl)) dfl in
      let c = if flat then c else fst (havoc c [] pl) in
      let spec (_,_,pl,d) =
        let kk c bl = let c, close = consume c pl bl in
                      close (vc true false d c []) in
        Bc (c, kk, substantial true false d c) in
      let cc, close = consume c pl (List.map spec dfl) in
      let impl (_,wr,pl,d) =
        let c,vl = havoc (if flat then c else cc) wr pl in
        w_forall vl (vc false pp d c []) in
      let w = vc pp dd e cc [] in
      if flat then w_and_l ((close w :: List.map impl dfl))
              else close (w_and_l (w :: List.map impl dfl))
  | Eset (e,vtl) -> assert (bl = []);
      let add cc (v,s) = c_add_vs cc v (c_inst_t c s) in
      vc pp dd e (List.fold_left add c vtl) bl
  | Ecut (f,e) -> assert (bl = []);
      (if pp && c.c_gl then w_and_asym else w_implies)
        (c_inst_t c f) (vc pp dd e c bl)
  | Ebox e -> assert (bl = []); vc dd dd e c bl
  | Ewox e -> assert (bl = []); vc pp pp e c bl
  | Eany   -> assert (bl = []); w_true

let vc e = (vc true true e c_empty []).wp

