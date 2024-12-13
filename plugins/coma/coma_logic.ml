(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Why3
open Wstdlib
open Ident
open Ty
open Term

(* First-order logic *)

let case_split = create_attribute "case_split"
let coma_solid = create_attribute "coma:solid"
let coma_weird = create_attribute "coma:weird"

let add_case_split t = t_attr_add case_split t
let add_stop_split t = t_attr_add stop_split t

let debug_slow = Debug.register_info_flag "coma_no_merge"
  ~desc:"Disable@ subgoal@ factorization."

let debug_triv = Debug.register_info_flag "coma_no_trivial"
  ~desc:"Discard@ trivial@ proof@ obligations."

let debug_recipe = Debug.register_info_flag "coma_print_recipes"
  ~desc:"Print@ intermediate@ verification@ conditions."

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
  | _, Ttrue, _  -> t_implies_simp  (t_not_simp f1) f3
  | _, Tfalse, _ -> t_and_asym_simp (t_not_simp f1) f3
  | _, _, Ttrue  -> t_implies_simp  f1 f2
  | _, _, Tfalse -> t_and_asym_simp f1 f2
  | _, _, _ -> t_if f1 f2 f3

let rec t_equ_simp t1 t2 = match t1.t_node, t2.t_node with
  | Tvar v1, Tvar v2 when vs_equal v1 v2 -> t_true
  | Tapp (s1,[]), Tapp (s2,[]) when ls_equal s1 s2 -> t_true
  | Tapp (s1,l1), Tapp (s2,l2) when s1.ls_constr > 0 && s2.ls_constr > 0 ->
      if ls_equal s1 s2 then List.fold_right2 (fun t1 t2 f ->
        t_and_simp (t_equ_simp t1 t2) f) l1 l2 t_true else t_false
  | Tconst c1, Tconst c2 when Constant.compare_const c1 c2 = 0 -> t_true
  | Tif (c,t1,e1), _ -> t_if_simp c (t_equ_simp t1 t2) (t_equ_simp e1 t2)
  | _, Tif (c,t2,e2) -> t_if_simp c (t_equ_simp t1 t2) (t_equ_simp t1 e2)
  | _, _ -> if Term.t_equal t1 t2 then t_true else Term.t_equ t1 t2

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

let rec t_solid p f =
  Sattr.mem stop_split f.t_attrs ||
  match f.t_node with
  | Tbinop (Tor,_,_) -> p
  | Tbinop (Tand,g,h) when p ->
      Sattr.mem asym_split g.t_attrs && t_solid p h
  | Tbinop (Timplies,_,h) when p -> t_solid p h
  | Tquant _ -> Sattr.mem coma_solid f.t_attrs
  | Tnot g -> t_solid (not p) g
  | _ -> true

let t_coma_quant q vl f =
  let g = t_quant_close_simp q vl [] f in
  if t_solid (q = Tforall) f then t_attr_add coma_solid g else g

let rec t_neg f =
  if Sattr.mem stop_split f.t_attrs then t_not_simp f
  else let tac = t_attr_copy f in match f.t_node with
    | Tnot g -> tac g
    | Tbinop (Tand,g,h) when Sattr.mem asym_split g.t_attrs ->
                              tac @@ t_implies g (t_neg h)
    | Tbinop (Tand,g,h) -> tac @@ t_or (t_neg g) (t_neg h)
    | Tbinop (Tor,g,h) -> tac @@ t_and (t_neg g) (t_neg h)
    | Tbinop (Timplies,g,h) ->    tac @@ t_and g (t_neg h)
    | Tquant (q,b) ->
        let q = if q = Texists then Tforall else Texists in
        let vl,tl,g = t_open_quant b in
        tac @@ t_quant_close q vl tl (t_neg g)
    | _ -> t_not_simp f

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
      let f = t_attr_remove coma_solid f (* no more useful *) in
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

(* Coma logic *)

type hsymbol = {
  hs_name : ident;
}

module Hsym = MakeMSHW (struct
  type t = hsymbol
  let tag hs = hs.hs_name.id_tag
end)

module Shs = Hsym.S
module Mhs = Hsym.M
module Hhs = Hsym.H
module Whs = Hsym.W

let hs_equal : hsymbol -> hsymbol -> bool = (==)
let hs_hash hs = id_hash hs.hs_name
let hs_compare hs1 hs2 = id_compare hs1.hs_name hs2.hs_name

let create_hsymbol id = { hs_name = Ident.id_register id }

let hs_tagged a h = Sattr.mem a h.hs_name.id_attrs

type wpsp = {
  wp: term;
  sp: term Mhs.t;
}

let w_true = { wp = t_true; sp = Mhs.empty }

let sp_or _ sp1 sp2 = Some (
  match sp1.t_node, sp2.t_node with
  | Ttrue, _ | _, Tfalse -> sp1
  | _, Ttrue | Tfalse, _ -> sp2
  | _ -> add_case_split (t_or sp1 sp2))

let w_and w1 w2 = {
  wp = t_and_simp w1.wp w2.wp;
  sp = Mhs.union sp_or w1.sp w2.sp
}

let rec w_and_l u = function [] -> u
  | w::wl -> w_and u (w_and_l w wl)

let w_and_l_rev = function [] -> w_true | [w] -> w
  | w::wl -> List.fold_left (fun a b -> w_and b a) w wl

let w_and_asym f w = {
  wp = t_and_asym_simp f w.wp;
  sp = Mhs.map (t_and_simp f) w.sp;
}

let w_implies f w = {
  wp = t_implies_simp f w.wp;
  sp = Mhs.map (t_and_simp f) w.sp;
}

let w_forall vl w = {
  wp = t_coma_quant Tforall vl w.wp;
  sp = Mhs.map (t_coma_quant Texists vl) w.sp
}

let w_forall vl w =
  if vl = [] then w else w_forall (List.rev vl) w

let w_subst s w = {
  wp = t_subst s w.wp;
  sp = Mhs.map (t_subst s) w.sp
}

let w_solid w =
  t_solid true w.wp &&
  Mhs.for_all (fun _ f -> t_solid false f) w.sp

(* Record splitting *)

let record_fields : (vsymbol list * vsymbol Mls.t) Wvs.t = Wvs.create 63

let rec complete_fields kn v =
  try let ts = match v.vs_ty.ty_node with
        | Tyapp (ts,_) -> ts | _ -> raise Exit in
      let cs,fl = match Decl.find_constructors kn ts
                  with [c] -> c | _ -> raise Exit in
      let fl = List.map (Opt.get_exn Exit) fl in
      let sb = ty_match_args v.vs_ty in
      let mk_vs f ty =
        let nm = v.vs_name.id_string ^ "'" ^ f.ls_name.id_string in
        let vs = create_vsymbol (id_fresh nm) (ty_inst sb ty) in
        complete_fields kn vs; vs in
      let vl = List.map2 mk_vs fl cs.ls_args in
      let fm = List.fold_right2 Mls.add fl vl Mls.empty in
      Wvs.set record_fields v (vl,fm)
  with Exit | Not_found -> ()

let complete_fields kn v =
  if not (Wvs.mem record_fields v) then complete_fields kn v

let inline_projections f =
  let rec simp lm f = match f.t_node with
    | Tapp (ls,[t]) when ls.ls_value <> None ->
        let t = simp lm t in
        t_attr_copy f (match t.t_node with
          | Tvar v ->
              (try t_var @@ Mls.find ls (try Mvs.find v lm
              with Not_found -> snd (Wvs.find record_fields v))
              with Not_found -> t_app ls [t] f.t_ty)
          | _ -> t_app ls [t] f.t_ty)
    | Tlet (t,b) ->
        let t = simp lm t in
        let u,s = t_open_bound b in
        let lm = match t.t_node with
          | Tvar v ->
              (try Mvs.add u (try Mvs.find v lm
              with Not_found -> snd (Wvs.find record_fields v)) lm
              with Not_found -> lm)
          | _ -> lm in
        t_attr_copy f (t_let_close_simp u t (simp lm s))
    | _ -> t_map (simp lm) f in
  simp Mvs.empty f

let split_record v s cvs =
  let rec fields ll lm cvs vl vfm s = match s.t_node with
    | Tapp (cs,tl) when cs.ls_constr = 1 ->
        List.fold_left2 (add_vt ll lm) cvs vl tl
    | Tvar u when Wvs.mem record_fields u ->
        let add cvs v u = add_vt ll lm cvs v (t_var u) in
        List.fold_left2 add cvs vl (fst (Wvs.find record_fields u))
    | Tvar u when Mvs.mem u lm ->
        fields ll lm cvs vl vfm (Mvs.find u lm)
    | Tlet (t,b) ->
        let u,f = t_open_bound b in
        fields ((s,u,t)::ll) (Mvs.add u t lm) cvs vl vfm f
    | _ ->
        let add f v cvs = add_vt ll lm cvs v (t_app_infer f [s]) in
        Mls.fold add vfm cvs
  and add_vt ll lm cvs v s =
    let relet s (f,u,t) = t_attr_copy f (t_let_close_simp u t s) in
    let cvs = Mvs.add v (List.fold_left relet s ll) cvs in
    try let vl,vfm = Wvs.find record_fields v in
        fields ll lm cvs vl vfm s
    with Not_found -> cvs
  in
  add_vt [] Mvs.empty cvs v s

(* Coma expressions *)

type param =
  | Pt of tvsymbol
  | Pv of vsymbol
  | Pr of vsymbol
  | Pc of hsymbol * vsymbol list * param list

type expr =
  | Esym of hsymbol
  | Eapp of expr * argument
  | Elam of param list * expr
  | Edef of expr * bool * defn list
  | Eset of expr * (vsymbol * term) list
  | Elet of expr * (vsymbol * term * bool) list
  | Ecut of term * bool * expr
  | Ebox of expr
  | Ewox of expr
  | Eany

and argument =
  | At of ty
  | Av of term
  | Ar of vsymbol
  | Ac of expr

and defn = hsymbol * vsymbol list * param list * expr

(* VC formulas *)

type formula =
  | Fsym of hsymbol
  | Fagt of formula * ty
  | Fagv of formula * term
  | Fagr of formula * vsymbol
  | Fagc of formula * formula
  | Fand of formula * formula
  | Fcut of term * bool * formula
  | Flam of param list * Shs.t * formula
  | Fall of param list * formula
  | Fneu of formula * Shs.t
  | Fany

type cache = {
  c_tv : ty Mtv.t;
  c_vs : term Mvs.t;
  c_hs : handler Mhs.t;
  c_ph : Shs.t;
  c_go : bool;
}

and handler = bool -> binding list -> wpsp

and binding =
  | Bt of ty
  | Bv of term
  | Bc of handler
  | Bu

let c_empty = {
  c_tv = Mtv.empty;
  c_vs = Mvs.empty;
  c_hs = Mhs.empty;
  c_ph = Shs.empty;
  c_go = true;
}

let c_find_vs c v = Mvs.find v c.c_vs

let c_inst_ty c t = ty_inst c.c_tv t
let c_inst_t  c s = t_ty_subst c.c_tv c.c_vs s

let c_clone_tv u = create_tvsymbol (id_clone u.tv_name)
let c_clone_vs c v =
  create_vsymbol (id_clone v.vs_name) (c_inst_ty c v.vs_ty)

let c_add_tv c u t = { c with c_tv = Mtv.add u t c.c_tv }
let c_add_vs c v s = { c with c_vs = split_record v s c.c_vs }

let c_add_hs c h d =
  let ph = if c.c_go then Shs.empty else Shs.add h c.c_ph in
  { c with c_hs = Mhs.add h d c.c_hs; c_ph = ph }

let c_neutralize c ph =
  let ph = if c.c_go then ph else Shs.inter c.c_ph ph in
  { c with c_go = false; c_ph = ph }

let c_call_hs c h go bl =
  Mhs.find h c.c_hs (go && (c.c_go || Shs.mem h c.c_ph)) bl

let no_bc bl = List.for_all (function
  | Bc _ -> false | Bt _ | Bv _ | Bu -> true) bl

let nasty check pl = List.exists (function
  | Pv _ | Pr _ -> false | Pt _ -> true
  | Pc (_,_,pl) -> check pl) pl

let unmergeable = nasty Util.ttrue
let unspeccable = nasty unmergeable

let wr_to_pl wr pl = List.fold_right (fun r pl -> Pr r :: pl) wr pl

let fold_on_pc fn acc pl = List.fold_left (fun acc -> function
  | Pc (h,wr,pl) -> fn acc h wr pl | Pt _ | Pv _ | Pr _ -> acc) acc pl

let hc_of_pl hc pl =
  fold_on_pc (fun hc h wr pl -> Mhs.add h (wr,pl) hc) hc pl

let lh_of_pl pl =
  fold_on_pc (fun lh h  _ _  -> Shs.add h lh)  Shs.empty pl

let mm_of_pl pl = fold_on_pc (fun mm h _ pl ->
  if unmergeable pl then mm else Shs.add h mm) Shs.empty pl

let rec f_and_l f = function [] -> f
  | g::gl -> Fand (f, f_and_l g gl)

let f_lambda ?(mm=Shs.empty) pl f =
  if pl = [] then f else match f with
    | Flam (ql,nm,f) -> Flam (pl @ ql, Shs.union mm nm, f)
    | _ -> Flam (pl,mm,f)

let f_all pl f =
  if pl = [] then f else match f with (* all pl . top <=> top *)
    | Fneu (f,ss) when Shs.is_empty ss -> Fneu (Fall (pl,f), ss)
    | Fall (ql,f) -> Fall (pl @ ql, f)
    | _ -> Fall (pl,f)

(* Pretty-printing (debug only) *)

let print_formula fmt e =
  let pp_p fmt = function
    | Pt tv -> Format.pp_print_char fmt '\''; Format.pp_print_string fmt tv.tv_name.id_string
    | Pv vs -> Format.pp_print_string fmt vs.vs_name.id_string
    | Pr vs -> Format.pp_print_char fmt '&'; Format.pp_print_string fmt vs.vs_name.id_string
    | Pc (hs,_,_) -> Format.pp_print_string fmt hs.hs_name.id_string in
  let rec pp fmt = function
    | Fsym h -> Format.pp_print_string fmt h.hs_name.id_string
    | Flam (pl,_,f) -> Format.fprintf fmt "@[<hov 2>(lambda %a .@ %a)@]"
        (Pp.print_list Pp.space pp_p) pl pp f
    | Fcut (s,true,f) -> Format.fprintf fmt "@[<hov 2>{ %a }@ %a@]"
        Pretty.print_term s pp f
    | Fcut (s,false,f) -> Format.fprintf fmt "@[<hov 2>-{ %a }-@ %a@]"
        Pretty.print_term s pp f
    | Fall (pl,f) -> Format.fprintf fmt "@[<hov 2>(forall %a .@ %a)@]"
        (Pp.print_list Pp.space pp_p) pl pp f
    | Fagt (f,t) -> Format.fprintf fmt "%a@ [%a]" pp f Pretty.print_ty t
    | Fagv (f,s) -> Format.fprintf fmt "%a@ [%a]" pp f Pretty.print_term s
    | Fagr (f,r) -> Format.fprintf fmt "%a@ [&%s]" pp f r.vs_name.id_string
    | Fagc (f,g) -> Format.fprintf fmt "%a@ (%a)" pp f pp g
    | Fand (f,g) -> Format.fprintf fmt "%a@ AND@ %a" pp f pp g
    | Fneu (f,ss) when Shs.is_empty ss -> Format.fprintf fmt "# (%a)" pp f
    | Fneu (f,ss) -> Format.fprintf fmt "#{%a} (%a)"
        (Pp.print_list Pp.space Format.pp_print_string)
        (List.map (fun hs -> hs.hs_name.id_string) (Shs.elements ss)) pp f
    | Fany -> Format.pp_print_string fmt "TOP" in
  pp fmt e

(* Formula evaluation *)

exception BadUndef of hsymbol

let rec joker h pl og go bl =
  if og && go then raise (BadUndef h);
  (* we only care about Pc and Bc *)
  let rec link wl pl bl = match pl,bl with
    | (Pt _ | Pv _ | Pr _) :: pl, bl
    | pl, (Bt _ | Bv _ | Bu) :: bl ->
        link wl pl bl
    | Pc (_,rl,ql)::pl, Bc k::bl ->
        let jj = jack false rl ql in
        link (k true jj :: wl) pl bl
    | _ -> w_and_l_rev wl in
  link [] pl bl

and jack go rl pl =
  let bl = List.map (function
    | Pt u -> Bt (ty_var (c_clone_tv u))
    | Pc (h,_,pl) -> Bc (joker h pl go)
    | Pv _ | Pr _ -> Bu) pl in
  List.fold_left (fun l _ -> Bu::l) bl rl

let rec consume mm c pl bl =
  let link (c,vl,hl) p b = match p,b with
    | Pt u, Bt t -> c_add_tv c u t, vl, hl
    | (Pv v | Pr v), Bv s -> c_add_vs c v s, vl, hl
    | (Pv v | Pr v), Bu -> let u = c_clone_vs c v in
                           c_add_vs c v (t_var u), u::vl, hl
    | Pc (h,wr,pl), Bc kk ->
        let hl,kk = factorize mm c hl h wr pl kk in
        c_add_hs c h kk, vl, hl
    | _ -> assert false in
  let rec fold (c,vl,hl as acc) pl bl = match pl,bl with
    | p::pl, b::bl -> fold (link acc p b) pl bl
    | [], bl -> c, vl, hl, bl
    | _ -> assert false in
  fold (c,[],[]) pl bl

and factorize mm c hl h wr pl kk =
  if Debug.test_flag debug_slow || unmergeable pl then hl,kk else
  let lz = lazy (prefact (Shs.mem h mm) c h (wr_to_pl wr pl) kk) in
  lz::hl, fun go bl -> if go then let lazy (_,_,_,zk) = lz in zk bl
                             else w_true

and prefact mh c h pl kk =
  let rec fields v (vz,zl,zv,vt) =
    let z = c_clone_vs c v in
    let zl,zv,vt = if mh then zl,zv,vt else try
      let ul,um = Wvs.find record_fields v in
      let vz,zl,zv,vt = List.fold_right fields ul (Mvs.empty,zl,zv,vt) in
      let vtoz u = try Mvs.find u vz with Not_found -> assert false in
      Wvs.set record_fields z (List.map vtoz ul, Mls.map vtoz um); zl,zv,vt
    with Not_found -> zl,zv,vt in
    Mvs.add v z vz, z::zl, Mvs.add z v zv, (v, t_var z)::vt in
  let [@warning "-8"] dup (Pv v|Pr v) (zl,zv,vt,bl) =
    let _,zl,zv,vt = fields v (Mvs.empty,zl,zv,vt) in
    zl, zv, vt, Bv (snd (List.hd vt))::bl in
  let zl,zv,vt,bl = List.fold_right dup pl ([],Mvs.empty,[],[]) in
  let zw = kk true bl in
  let abort_mh = mh && w_solid zw in let mh = mh && not abort_mh in
  let [@warning "-8"] ripe (Pv v|Pr v) = Wvs.mem record_fields v in
  if abort_mh && List.exists ripe pl then prefact mh c h pl kk else
  let h = if mh then create_hsymbol (id_clone h.hs_name) else h in
  h, zl, zw, fun bl ->
    let sph f = {wp = t_true; sp = Mhs.singleton h f} in
    if pl = [] then if mh then sph t_true else zw else
    let c,ul,_,_ = consume Shs.empty c pl bl in
    let link (v,t) = t_equ t (c_find_vs c v) in
    w_forall ul (if mh then sph (t_and_l (List.map link vt))
                 else w_subst (Mvs.map (c_find_vs c) zv) zw)

let close vl hl {wp;sp} =
  let pile (vl,wl,sh) (lazy (h,zl,zw,_)) =  match Mhs.find h sp with
    | f -> List.rev_append zl vl, w_implies f zw :: wl, Shs.add h sh
    | exception Not_found -> vl,wl,sh in
  let pile a lz = if Lazy.is_val lz then pile a lz else a in
  let vl,wl,sh = List.fold_left pile (vl,[],Shs.empty) hl in
  w_forall vl @@ w_and_l {wp; sp = Mhs.set_diff sp sh} wl

let rec f_eval c o bl = match o with
  | Fsym h -> c_call_hs c h true bl
  | Flam (pl, mm, f) ->
      let c,vl,hl,bl = consume mm c pl bl in
      close vl hl (f_eval c f bl)
  | Fcut (s, pp, f) ->
      (if pp && c.c_go then w_and_asym else w_implies)
        (add_stop_split (c_inst_t c s)) (f_eval c f bl)
  | Fall (pl,f) -> f_eval c (f_lambda pl f) (jack c.c_go [] pl)
  | Fand (f, g) -> w_and (f_eval c f bl) (f_eval c g bl)
  | Fagt (f, t) -> f_eval c f (Bt (c_inst_ty c t) :: bl)
  | Fagv (f, s) -> f_eval c f (Bv (c_inst_t  c s) :: bl)
  | Fagr (f, r) -> f_eval c f (Bv (c_find_vs c r) :: bl)
  | Fagc (f, g) -> f_eval c f (Bc (f_handler c g) :: bl)
  | Fneu (f,ss) -> f_pass (c_neutralize c ss) f bl
  | Fany -> w_true

and f_pass ({c_go = go; c_ph = ph} as c) o bl =
  if not go && Shs.is_empty ph && no_bc bl then w_true
  else f_eval c o bl

and f_handler c o go bl =
  f_pass (if go then c else c_neutralize c Shs.empty) o bl

let rec fill_mm lh = function
  | Fsym h as f ->
      (try incr (Mhs.find h lh) with Not_found -> ()); f
  | Flam (pl, mm, f) ->
      let mm = Shs.inter mm (lh_of_pl pl) in
      let mm = Mhs.map (fun _ -> ref 0) mm in
      let f = fill_mm (Mhs.set_union mm lh) f in
      let check r = if !r > 1 then Some () else None in
      Flam (pl, Mhs.map_filter check mm, f)
  | Fcut (s, pp, f) -> Fcut (s, pp, fill_mm lh f)
  | Fall (pl,f) -> Fall (pl, fill_mm lh f)
  | Fagt (f, t) -> Fagt (fill_mm lh f, t)
  | Fagv (f, s) -> Fagv (fill_mm lh f, s)
  | Fagr (f, r) -> Fagr (fill_mm lh f, r)
  | Fagc (f, g) -> Fagc (fill_mm lh f, fill_mm lh g)
  | Fand (f, g) -> Fand (fill_mm lh f, fill_mm lh g)
  | Fneu (f,ss) -> Fneu (fill_mm (Mhs.set_inter lh ss) f, ss)
  | Fany -> Fany

let rec scan_fields kn pl = List.iter (function
  | Pc (_,wr,pl) -> List.iter (complete_fields kn) wr;
                    scan_fields kn pl
  | Pv v | Pr v  -> complete_fields kn v
  | Pt _ -> ()) pl

let rec quick_fields kn = function
  | Fsym _ as f -> f
  | Flam (pl, mm, f) -> scan_fields kn pl; Flam (pl, mm, quick_fields kn f)
  | Fcut (s, pp, f) -> Fcut (inline_projections s, pp, quick_fields kn f)
  | Fall (pl,f) -> scan_fields kn pl; Fall (pl, quick_fields kn f)
  | Fagt (f, t) -> Fagt (quick_fields kn f, t)
  | Fagv (f, s) -> Fagv (quick_fields kn f, inline_projections s)
  | Fagr (f, r) -> Fagr (quick_fields kn f, r)
  | Fagc (f, g) -> Fagc (quick_fields kn f, quick_fields kn g)
  | Fand (f, g) -> Fand (quick_fields kn f, quick_fields kn g)
  | Fneu (f,ss) -> Fneu (quick_fields kn f, ss)
  | Fany -> Fany

let top_eval kn c f =
  let f = fill_mm Mhs.empty f in
  Debug.dprintf debug_recipe "@[%a@]@." print_formula f;
  vc_simp (f_eval c (quick_fields kn f) []).wp

let top_handler kn c f =
  let f = fill_mm Mhs.empty f in
  Debug.dprintf debug_recipe "@[%a@]@." print_formula f;
  f_handler c (quick_fields kn f)

let rec drop_attr at = function
  | Fcut (s,pp,f) ->  let s = if pp then t_attr_remove at s else s in
                      Fcut (s, pp, drop_attr at f)
  | Flam (pl,mm,f) -> Flam (pl, mm, drop_attr at f)
  | o -> o

(* VC generation *)

type vc = TT of formula | TB of formula * formula

let of_tt = function
  | TT f -> f | TB _ -> invalid_arg "of_tt"

let of_tb = function
  | TT _ -> invalid_arg "of_tb" | TB (f,g) -> f,g

let vc_map fn = function
  | TT f -> TT (fn f) | TB (f,g) -> TB (fn f, fn g)

let vc_map2 fn v w = match v,w with
  | TT vf, TT wf -> TT (fn vf wf)
  | TB (vf,vg), TB(wf,wg)  -> TB (fn vf wf, fn vg wg)
  | _ -> invalid_arg "vc_map2"

let dl_split flat pl dl =
  if flat || List.length dl = 1 then [pl,dl] else
  let [@warning "-8"] head (Pc (h,_,_),_) = h in
  let iter fn (_,g) =
    let rec inspect sh = function
      | Fsym h -> if not (Shs.mem h sh) then fn h
      | Flam (pl,_,f) | Fall (pl,f) ->
          inspect (Shs.union sh (lh_of_pl pl)) f
      | Fcut (_,_,f) | Fneu (f,_) | Fagt (f,_)
      | Fagv (f,_) | Fagr (f,_) -> inspect sh f
      | Fagc (f,g) | Fand (f,g) -> inspect sh f; inspect sh g
      | Fany -> () in
    inspect Shs.empty g in
  let module SCC = MakeSCC(Hhs) in
  List.map (fun (_,dl) -> List.split dl) @@
    SCC.scc head iter @@ List.combine pl dl

let rec vc tt hc o al =
  let rec apply w mr pl al = match pl,al with
    | (Pt _)::pl, (At t)::al ->
        apply (vc_map (fun f -> Fagt (f,t)) w) mr pl al
    | (Pv _)::pl, (Av s)::al ->
        apply (vc_map (fun f -> Fagv (f,s)) w) mr pl al
    | (Pr p)::pl, (Ar r)::al ->
        let mr = Mvs.add p r mr in
        apply (vc_map (fun f -> Fagr (f,r)) w) mr pl al
    | (Pc (_,wr,_))::pl, (Ac d)::al ->
        let param r = Pr (Mvs.find_def r r mr) in
        let wr = List.map param wr in
        let alam f g = Fagc (f, f_lambda wr g) in
        apply (vc_map2 alam w (vc tt hc d [])) mr pl al
    | _, [] -> w | _ -> assert false in
  match o with
  | Eapp (e,a) ->
      vc tt hc e (a::al)
  | Esym h ->
      let (wr,pl) = Mhs.find h hc in
      let f = List.fold_left (fun f r -> Fagr (f,r)) (Fsym h) wr in
      let w = if tt then TT f else TB (f, Fneu (f, Shs.empty)) in
      apply w Mvs.empty pl al
  | Elam (pl,e) ->
      let lh = lh_of_pl pl and mm = mm_of_pl pl in
      let w = match vc tt (hc_of_pl hc pl) e [] with
        | TB (f,g) when not (Shs.is_empty lh) ->
            TB (Fand(f,Fneu(g,lh)), Fand(Fneu(f,lh),g))
        | w -> w in
      apply (vc_map (f_lambda ~mm pl) w) Mvs.empty pl al
  | Edef (e,flat,dfl) ->
      let agc f g      = Fagc (f, g) in
      let agc_init f g = Fagc (f, drop_attr Vc.expl_loop_keep g) in
      let agc_keep f g = Fagc (f, drop_attr Vc.expl_loop_init g) in
      let pl,ll,fl,gl = vc_defn tt hc flat dfl in
      let loop = not (flat || unspeccable pl) in
      let mm = if flat then mm_of_pl pl else
               if loop then lh_of_pl pl else Shs.empty in
      let bind agc f = List.fold_left (fun f (pl,gl) ->
        List.fold_left agc (f_lambda ~mm pl f) gl) f ll in
      let make f fl = match fl with
        | h::hl when loop ->
            let ip = bind agc_keep (f_and_l h hl) in
            f_all pl (Fand (bind agc_init f, ip))
        | _ when flat -> f_and_l (bind agc f) fl
        | _ -> f_all pl (bind agc (f_and_l f fl)) in
      (match vc tt (hc_of_pl hc pl) e [] with
       | TB (f,g) -> TB (make f fl, make g gl)
       | TT f -> TT (make f fl))
  | Eset (e,vtl) ->
      let agv f (_,s) = Fagv (f, s) in
      let pl = List.map (fun (v,_) -> Pv v) vtl in
      let agv f = List.fold_left agv (f_lambda pl f) vtl in
      vc_map agv (vc tt hc e [])
  | Elet (e,vtl) ->
      let agv f (_,s,_) = Fagv (f,s) in
      let pl = List.map (fun (v,_,_) -> Pv v) vtl in
      let agv f = List.fold_left agv (f_lambda pl f) vtl in
      vc_map agv (vc tt hc e [])
  | Ecut (f,b,e) ->
      (match vc tt hc e [] with TT g -> TT (Fcut (f,b,g))
        | TB (g,h) -> TB (Fcut (f,b,g), Fcut (f,false,h)))
  | (Ebox e | Ewox e) when tt -> vc true hc e []
  | Ebox e -> TB (Fany, of_tt (vc true hc e []))
  | Ewox e -> TB (of_tt (vc true hc e []), Fany)
  | Eany -> if tt then TT Fany else TB (Fany, Fany)

and vc_defn tt hc flat dfl =
  let pl = List.map (fun (h,wr,pl,_) -> Pc (h,wr,pl)) dfl in
  let hc = if flat then hc else hc_of_pl hc pl in
  let ll,fl,gl = List.fold_right (fun (h,wr,pl,d) (ll,fl,gl) ->
    let weird = not tt && hs_tagged coma_weird h in
    let pl = wr_to_pl wr pl in let mm = mm_of_pl pl in
    let tb,bt = of_tb (vc false (hc_of_pl hc pl) d []) in
    let fl = if weird then fl else f_all pl bt :: fl in
    let gl = if weird then f_all pl bt :: gl else gl in
    f_lambda ~mm pl tb :: ll, fl, gl) dfl ([],[],[]) in
  pl, dl_split flat pl ll, fl, gl

let rec fill_wox rb = function
  | Esym _ | Eany as o -> o
  | Elam (pl, e) -> Elam (pl, fill_wox rb e)
  | Edef (e, flat, dfl) ->
      let dfl = wox_defn dfl in
      let wd = List.exists (fun (h,_,_,d) ->
        hs_tagged coma_weird h && match d with
          | Ewox _ -> false | _ -> true) dfl in
      Edef ((if wd then (rb := true; wox_expr e)
                  else fill_wox rb e), flat, dfl)
  | Eset (e, vtl) -> Eset (fill_wox rb e, vtl)
  | Elet (e, vtl) -> Elet (fill_wox rb e, vtl)
  | Ecut (f, b, e) -> Ecut (f, b, fill_wox rb e)
  | Eapp (e, Ac d) -> Eapp (fill_wox rb e, Ac (fill_wox rb d))
  | Eapp (e, (At _|Av _|Ar _ as a)) -> Eapp (fill_wox rb e, a)
  | Ebox e -> rb := true; Ebox (fill_wox rb e)
  | Ewox e -> Ewox (fill_wox (ref false) e)

and wox_defn dfl =
  List.map (fun (h,wr,pl,d) -> h, wr, pl, wox_expr d) dfl

and wox_expr e =
  let rb = ref false in
  let e = fill_wox rb e in
  if !rb then e else Ewox e

(* Effect inference *)

exception CollisionHs of hsymbol
exception CollisionRs of vsymbol

let rec fill_wr hc lh lr wm o al =
  let join_writes wr wmd =
    let wmd = if wr = [] then wmd else
      Mhs.map (Svs.union (Svs.of_list wr)) wmd in
    let add _ s1 s2 = Some (Svs.union s1 s2) in
    wm := Mhs.union add !wm wmd in
  let prewrite wr d =
    let wmd = ref Mhs.empty in
    let d = fill_wr hc lh lr wmd d [] in
    join_writes wr !wmd; d in
  let rec apply w mr pl al = match pl,al with
    | (Pt _ | Pv _)::pl, (At _ | Av _ as a)::al ->
        apply (Eapp (w, a)) mr pl al
    | (Pr p)::pl, (Ar r as a)::al ->
        apply (Eapp (w, a)) (Mvs.add p r mr) pl al
    | (Pc (_,wr,_))::pl, (Ac d)::al ->
        let inst r = Mvs.find_def r r mr in
        let d = prewrite (List.map inst wr) d in
        apply (Eapp (w, Ac d)) mr pl al
    | _, [] -> w | _ -> assert false in
  match o with
  | Eapp (e,a) ->
      fill_wr hc lh lr wm e (a::al)
  | Esym h ->
      let lc,(_,pl) = try true, Mhs.find h lh
        with Not_found -> false, Mhs.find h hc in
      if lc && not (Mhs.mem h !wm) then
        wm := Mhs.add h Svs.empty !wm;
      apply o Mvs.empty pl al
  | Elam (pl, e) ->
      let pl, e = wr_lambda hc lh lr wm pl e in
      apply (Elam (pl, e)) Mvs.empty pl al
  | Edef (e, flat, dfl) ->
      let dwl = wr_defn hc lh lr flat dfl in
      let mkp ((h,wr,ql,_), _) = Pc (h,wr,ql) in
      let pl,e = wr_lambda hc lh lr wm (List.map mkp dwl) e in
      let [@warning "-8"] move (Pc (_,wr,_)) ((h,_,ql,d), wmd) =
        join_writes wr wmd; h,wr,ql,d in
      let dfl = List.map2 move pl dwl in
      let rec fixpoint dfl =
        let same = ref true in
        let on_def (h,ur,pl,d as df) (_,wmd) =
          let wr = Svs.inter lr (Mhs.find_def Svs.empty h !wm)
          and ur = Svs.of_list ur in
          if Svs.subset wr ur then df else
          let wr = Svs.elements (Svs.union wr ur) in
          join_writes wr wmd; same := false; h,wr,pl,d in
        let dfl = List.map2 on_def dfl dwl in
        if not !same then fixpoint dfl else begin
        wm := Mhs.set_diff !wm (lh_of_pl pl); dfl end in
      Edef (e, flat, if flat then dfl else fixpoint dfl)
  | Eset (e, vtl) ->
      Eset (prewrite (List.map fst vtl) e, vtl)
  | Elet (e, vtl) ->
      let add lr (r,_,b) =
        if b then Svs.add r lr else lr in
      let lr = List.fold_left add lr vtl in
      Elet (fill_wr hc lh lr wm e al, vtl)
  | Ecut (phi, b, e) ->
      Ecut (phi, b, fill_wr hc lh lr wm e al)
  | Ebox e -> Ebox (fill_wr hc lh lr wm e al)
  | Ewox e -> Ewox (fill_wr hc lh lr wm e al)
  | Eany -> Eany

and wr_lambda hc lh lr wm pl e =
  let llr = List.fold_left (fun lr -> function
    | Pr r -> Svs.add_new (CollisionRs r) r lr
    | Pt _ | Pv _ | Pc _ -> lr) lr pl in
  let sh = List.fold_left (fun sh -> function
    | Pc (h,_,ql) -> Mhs.add h ([],ql) sh
    | Pt _ | Pv _ | Pr _ -> sh) Mhs.empty pl in
  let die h _ _ = raise (CollisionHs h) in
  let lh = Mhs.union die lh sh in
  let e = fill_wr hc lh llr wm e [] in
  let update lr = function
    | Pt _ | Pv _ as p -> lr, p
    | Pr r as p -> Svs.add r lr, p
    | Pc (h,_wr,ql) -> (* TODO: warning? *)
        let wr = Mhs.find_def Svs.empty h !wm in
        let wr = Svs.elements (Svs.inter wr lr) in
        lr, Pc (h, wr, ql) in
  let _,pl = Lists.map_fold_left update lr pl in
  wm := Mhs.set_diff !wm sh;
  pl, e

and wr_defn hc lh lr flat dfl =
  let on_def lh (h,wr,pl,d) =
    let pl = List.map (function
      | Pt _ | Pv _ | Pr _ as p -> p
      | Pc (h,_,l) -> Pc (h,[],l)) pl in
    Mhs.add h (wr,pl) lh, (h,wr,pl,d) in
  let lh, dfl = if flat then lh, dfl else
    Lists.map_fold_left on_def lh dfl in
  let same_p p q = match p,q with
    | Pc (_,wr,_), Pc (_,vr,_) ->
        Lists.equal vs_equal wr vr
    | _, _ -> true in
  let rec fixpoint lh dfl =
    let same = ref true in
    let on_def lh ((h,wr,ql,d),wmd) =
      let wmd = ref wmd in
      let pl, d = wr_lambda hc lh lr wmd ql d in
      same := !same && List.for_all2 same_p pl ql;
      Mhs.add h (wr,pl) lh, ((h,wr,pl,d),!wmd) in
    let lh, dfl = Lists.map_fold_left on_def lh dfl in
    if flat || !same then dfl else fixpoint lh dfl in
  fixpoint lh (List.map (fun d -> d,Mhs.empty) dfl)

let wr_expr hc e =
  fill_wr hc Mhs.empty Svs.empty (ref Mhs.empty) e []

let wr_defn hc flat dfl =
  List.map fst (wr_defn hc Mhs.empty Svs.empty flat dfl)

(* Top-level Coma definitions *)

type context = Decl.known_map * (vsymbol list * param list) Mhs.t * cache

let c_empty = Mid.empty, Mhs.empty, c_empty

let c_merge (kno,hco,co) (knn,hcn,cn) =
  Mid.set_union knn kno,
  Mhs.set_union hcn hco,
  { c_tv = Mtv.set_union cn.c_tv co.c_tv;
    c_vs = Mvs.set_union cn.c_vs co.c_vs;
    c_hs = Mhs.set_union cn.c_hs co.c_hs;
    c_ph = Shs.empty;
    c_go = true }

let c_known (_,hc,c) kn = kn, hc, c

let vc_expr (kn,hc,c) e =
  top_eval kn c @@ of_tt @@ vc true hc (wox_expr (wr_expr hc e)) []

let vc_defn (kn,hc,c) flat dfl =
  let dfl = wox_defn (wr_defn hc flat dfl) in
  let pl,ll,fl,_ = vc_defn true hc flat dfl in
  let ctx c pl bl = let c,_,_,_ = consume Shs.empty c pl bl in c in
  let bl_of_gl c gl = List.map (fun g -> Bc (top_handler kn c g)) gl in
  let cc = if flat then c else ctx c pl (jack true [] pl) in
  let add_dl (pl,gl) c = ctx c pl (bl_of_gl c gl) in
  let c = List.fold_right add_dl ll cc in
  let eval (h,_,_,_) f = h, top_eval kn (if flat then cc else c) f in
  let keep (_,f) = not (Debug.test_flag debug_triv && is_true f) in
  (kn, hc_of_pl hc pl, c), List.filter keep (List.map2 eval dfl fl)

let extspec_attr = create_attribute "coma:extspec"

let vc_spec (_,hc,c) h =
  if not (hs_tagged extspec_attr h) then [] else
  let wr, pl = Mhs.find h hc in
  if unspeccable pl then [] else
  let n = h.hs_name.id_string in
  let id_pre = id_fresh (n ^ "'pre") in
  let y = Bc (fun _ _ -> w_true) in
  let param (ul,bl,outs) = function
    | Pt _ -> assert false
    | Pv v | Pr v -> let u = c_clone_vs c v in let b = Bv (t_var u) in
        u::ul, b::bl, List.map (fun (id,ul,bl) -> id, u::ul, b::bl) outs
    | Pc ({hs_name = {id_string = s}},wr,pl) ->
        let pl = wr_to_pl wr pl in
        let [@warning "-8"] add (zl,fl) (Pv v|Pr v) =
          let z = c_clone_vs c v in
          z::zl, t_equ (t_var z) (t_var v) :: fl in
        let zl,fl = List.fold_left add (ul,[]) pl in
        let f = t_not_simp (t_and_l (List.rev fl)) in
        let kk go bl = if not go then w_true else
          let c,_,_,_ = consume Shs.empty c pl bl in
          { wp = c_inst_t c f; sp = Mhs.empty } in
        let oo = id_fresh (n ^ "'post'" ^ s), zl, Bc kk::bl in
        ul, y::bl, oo :: List.map (fun (id,ul,bl) -> id, ul, y::bl) outs
  in
  let ul,bl,outs = List.fold_left param ([],[],[]) (wr_to_pl wr pl) in
  let call go ul bl = spec_simp ul (c_call_hs c h go (List.rev bl)).wp in
  (id_pre, List.rev ul, call true ul bl) :: List.rev_map (fun (id,ul,bl) ->
       id, List.rev ul, t_neg (call false ul bl)) outs

let () = Exn_printer.register (fun fmt -> function
  | BadUndef h -> Format.fprintf fmt
      "Handler `%s' is used in an illegal position" h.hs_name.id_string
  | CollisionHs h -> Format.fprintf fmt
      "Handler `%s' is introduced twice in an expression" h.hs_name.id_string
  | CollisionRs r -> Format.fprintf fmt
      "Reference `%s' is introduced twice in an expression" r.vs_name.id_string
  | exn -> raise exn)
