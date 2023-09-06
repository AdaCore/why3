(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2023 --  Inria - CNRS - Paris-Saclay University  *)
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

type hsymbol = {
  hs_name : ident;
}

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

let create_hsymbol id = { hs_name = id_register id }

(*
let t_and_simp = t_and
let t_and_simp_l = t_and_l
let t_and_asym_simp = t_and_asym
let t_implies_simp = t_implies
let t_forall_close_simp = t_forall_close
*)

type wpsp = {
  wp: term;
  sp: term Mhs.t;
}

let w_true = { wp = t_true; sp = Mhs.empty }

let w_and w1 w2 = {
  wp = t_and_simp w1.wp w2.wp;
  sp = Mhs.union (fun _ f1 f2 -> Some (t_or_simp f1 f2)) w1.sp w2.sp
}

let w_and_l wl = List.fold_right w_and wl w_true

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
  | Ecut of term * expr
  | Ebox of expr
  | Ewox of expr
  | Eany

and argument =
  | At of ty
  | Av of term
  | Ar of vsymbol
  | Ac of expr

and defn = hsymbol * vsymbol list * param list * expr

type context = {
  c_tv : ty Mtv.t;
  c_vs : term Mvs.t;
  c_hs : closure Mhs.t;
  c_lc : Shs.t;
  c_gl : bool;
}

and closure = (* Co for outcomes (= lambdas), Cd for definitions *)
  | Co of bool * bool * context * vsymbol Mvs.t *              expr
  | Cd of bool * bool * context * vsymbol Mvs.t * param list * expr
  | Cz of               hsymbol * vsymbol Mvs.t * param list

type binding =
  | Bt of ty
  | Bv of term
  | Br of term * vsymbol
  | Bc of bool * bool * context * expr

let c_empty = {
  c_tv = Mtv.empty;
  c_vs = Mvs.empty;
  c_hs = Mhs.empty;
  c_lc = Shs.empty;
  c_gl = true;
}

let t_inst c t = ty_inst c.c_tv t
let v_inst c t = t_ty_subst c.c_tv c.c_vs t
let r_inst c r = t_ty_subst c.c_tv c.c_vs (t_var r)

let c_add_t c u t = { c with c_tv = Mtv.add u t c.c_tv }
let c_add_v c v t = { c with c_vs = Mvs.add v t c.c_vs }

let c_add_h out (c,zl,hl,map) h pp dd cc wr pl e =
  let lc = if c.c_gl then Shs.empty else Shs.add h c.c_lc in
  let rec solid = function
    | Elam (_,e) | Eset (e,_) | Ecut (_,e) -> solid e
    | Edef (e,_,_) when not pp -> solid e
(*     | Ebox _ when not dd -> false *)
    | Ewox _ when not pp -> false
    | Eany -> false
    | _ -> true in
  if  (let s = h.hs_name.id_string in s <> "" && s.[0] = '_') &&
      List.for_all (function Pv _ | Pr _ -> true | Pt _ | Pc _ -> false) pl &&
      (cc.c_gl || not (Shs.is_empty cc.c_lc)) &&
      solid e
  then
    let hc = create_hsymbol (id_clone h.hs_name) in
    let clone v = create_vsymbol (id_clone v.vs_name) (t_inst c v.vs_ty) in
    let zm = List.fold_left (fun zm v -> Mvs.add v (clone v) zm) Mvs.empty wr in
    let zm = List.fold_left (fun zm -> function Pt _ | Pc _ -> assert false
      | Pv v | Pr v -> Mvs.add v (clone v) zm) zm pl in
    let bl = if out then List.map (function Pt _ | Pc _ -> assert false
      | Pr v -> Br (t_var (Mvs.find v zm), v (* irrelevant *))
      | Pv v -> Bv (t_var (Mvs.find v zm))) pl else [] in
    let link up r = Mvs.add (Mvs.find_def r r map) (t_var (Mvs.find r zm)) up in
    let up = if out then List.fold_left link Mvs.empty wr else Mvs.map t_var zm in
    let cc = { cc with c_vs = Mvs.set_union up cc.c_vs } in
    { c with c_hs = Mhs.add h (Cz (hc,zm,pl)) c.c_hs; c_lc = lc},
    Mvs.fold (fun _ z zl -> z::zl) zm zl, (hc,pp,dd,cc,bl,e)::hl, map
  else
    let wr = List.fold_left (fun wr r ->
      Mvs.add (Mvs.find_def r r map) r wr) Mvs.empty wr in
    let cl = if out then Co (pp, dd, cc, wr, e)
                    else Cd (pp, dd, cc, wr, pl, e) in
    { c with c_hs = Mhs.add h cl c.c_hs; c_lc = lc },zl,hl,map

let consume c pl bl =
  let eat (c,zl,hl,m as acc) p b = match p, b with
    | Pt u, Bt t -> c_add_t c u t, zl, hl, m
    | Pv v, Bv t -> c_add_v c v t, zl, hl, m
    | Pr p, Br (q,r) -> c_add_v c p q, zl, hl, Mvs.add p r m
    | Pc (h,wr,pl), Bc (pp,dd,cc,e) -> c_add_h true acc h pp dd cc wr pl e
    | _ -> assert false in
  List.fold_left2 eat (c,[],[],Mvs.empty) pl bl

let rec vc pp dd c bl = function
  | Esym h ->
      let safe = pp && (c.c_gl || Shs.mem h c.c_lc) in
      let update cc wr = { cc with
        c_gl = safe && cc.c_gl;
        c_lc = if safe then cc.c_lc else Shs.empty;
        c_vs = Mvs.set_union (Mvs.map (r_inst c) wr) cc.c_vs } in
      begin match Mhs.find h c.c_hs with
      | Co (pp, dd, cc, wr, d) ->
          vc pp dd (update cc wr) bl d
      | Cd (pp, dd, cc, wr, pl, d) ->
          let cc,zl,hl,_ = consume (update cc wr) pl bl in
          discharge (vc pp dd cc [] d) zl hl
      | Cz (h, zm, pl) when safe ->
          let c,_,_,_ = consume c pl bl in
          let add v z f = t_and_simp (t_equ (t_var z) (r_inst c v)) f in
          { wp = t_true; sp = Mhs.singleton h (Mvs.fold add zm t_true) }
      | Cz _ -> w_true
      end
  | Eapp (e, a) ->
      let b = match a with
        | At t -> Bt (t_inst c t)
        | Av t -> Bv (v_inst c t)
        | Ar r -> Br (r_inst c r, r)
        | Ac d -> Bc (pp,dd,c,d) in
      vc pp dd c (b::bl) e
  | Elam (pl, e) ->
      let c,zl,hl,_ = consume c pl bl in
      let lc = List.fold_left (fun s -> function
        | Pc (h,_,_) -> Shs.add h s
        | Pt _ | Pv _ | Pr _ -> s) Shs.empty pl in
      let cw = { c with c_lc = lc; c_gl = false } in
      let w = w_and (vc pp dd c [] e) (vc (not pp) (not dd) cw [] e) in
      discharge w zl hl
  | Edef (e, flat, dfl) -> assert (bl = []);
      let cr = if flat then c else
        let pc_of_def (h,wr,pl,_) = Pc (h,wr,pl) in
        fst (havoc c [] (List.map pc_of_def dfl)) in
      let spec c (h,w,l,d) = c_add_h false c h true false cr w l d in
      let cl,zl,hl,_ = List.fold_left spec (c,[],[],Mvs.empty) dfl in
      let impl (_,wr,pl,d) =
        let c,vl = havoc (if flat then c else cl) wr pl in
        w_forall vl (vc false pp c [] d) in
      let wl = vc pp dd cl [] e :: List.map impl dfl in
      discharge (w_and_l wl) zl hl
  | Eset (e, vtl) -> assert (bl = []);
      let set cl (v,t) = c_add_v cl v (v_inst c t) in
      vc pp dd (List.fold_left set c vtl) [] e
  | Ecut (f, e) -> assert (bl = []);
      (if pp && c.c_gl then w_and_asym else w_implies)
        (v_inst c f) (vc pp dd c [] e)
  | Ebox e -> assert (bl = []); vc dd dd c [] e
  | Ewox e -> assert (bl = []); vc pp pp c [] e
  | Eany   -> assert (bl = []); w_true

and discharge w zl hl =
  let wl = List.map (fun (h,pp,dd,c,bl,e) ->
    let sp = Mhs.find_def t_false h w.sp in
    w_implies sp (vc pp dd c bl e)) hl in
  let drop s (h,_,_,_,_,_) = Mhs.remove h s in
  let w = { w with sp = List.fold_left drop w.sp hl } in
  w_forall (List.rev zl) (w_and_l (w :: List.rev wl))

and havoc c wr pl =
  let on_write (vl,c) p =
    let q = Mvs.find p c.c_vs in
    let id = id_clone (match q.t_node with
      | Tvar v -> v | _ -> p).vs_name in
    let r = create_vsymbol id (t_type q) in
    r::vl, c_add_v c p (t_var r) in
  let on_param (vl,c) = function
    | Pt u ->
        let v = create_tvsymbol (id_clone u.tv_name) in
        vl, c_add_t c u (ty_var v)
    | Pv v | Pr v ->
        let ty = t_inst c v.vs_ty in
        let u = create_vsymbol (id_clone v.vs_name) ty in
        u::vl, c_add_v c v (t_var u)
    | Pc (h,wr,pl) ->
        let d = Ecut (t_false, Eany) in
        let dl = List.filter_map (function
          | Pc (h,wr,pl) ->
              let apply d p = Eapp (d, match p with
                | Pt u -> At (ty_var u)
                | Pv v -> Av (t_var v)
                | Pr r -> Ar r
                | Pc (g,_,_) -> Ac (Esym g)) in
              let d = List.fold_left apply (Esym h) pl in
              Some (h, wr, pl, Ebox d)
          | Pt _ | Pv _ | Pr _ -> None) pl in
        let d = if dl = [] then d else Edef (d,true,dl) in
        let c,_,_,_ = c_add_h false (c,[],[],Mvs.empty)
                              h true true c wr pl d in
        vl, c in
  let vl,c = List.fold_left on_write ([],c) wr in
  let vl,c = List.fold_left on_param (vl,c) pl in
  c, List.rev vl

let vc e = (vc true true c_empty [] e).wp

let (!) h = Esym h

let (--) e t = Eapp (e, At t)
let (-+) e t = Eapp (e, Av t)
let (-&) e r = Eapp (e, Ar r)
let (-*) e d = Eapp (e, Ac d)

let (<>) e vtl         = Eset (e,vtl)
let (>>) e (h,wr,pl,d) = Edef (e,true, [h,wr,pl,d])
let (<<) e (h,wr,pl,d) = Edef (e,false,[h,wr,pl,d])

let def h wr pl d = (h,wr,pl,d)
let lam pl d = Elam (pl,d)

let cut f d = Ecut (f,d)

let hs_halt = create_hsymbol (id_fresh "halt")
let hs_fail = create_hsymbol (id_fresh "fail")

let hs_alloc = create_hsymbol (id_fresh "alloc")
let hs_assign = create_hsymbol (id_fresh "assign")

let hs_if = create_hsymbol (id_fresh "if")
let hs_then = create_hsymbol (id_fresh "then")
let hs_else = create_hsymbol (id_fresh "else")

let hs_ret = create_hsymbol (id_fresh "ret")
let hs_out = create_hsymbol (id_fresh "out")
let hs_loop = create_hsymbol (id_fresh "loop")
let hs_ret_ = create_hsymbol (id_fresh "_ret")

let vs_ii = create_vsymbol (id_fresh "i") ty_int
let vs_ji = create_vsymbol (id_fresh "j") ty_int
(*
let vs_ki = create_vsymbol (id_fresh "k") ty_int
let vs_li = create_vsymbol (id_fresh "l") ty_int
let vs_mi = create_vsymbol (id_fresh "m") ty_int
*)
let vs_pi = create_vsymbol (id_fresh "p") ty_int
let vs_qi = create_vsymbol (id_fresh "q") ty_int

let vs_bb = create_vsymbol (id_fresh "b") ty_bool

let tv_a = tv_of_string "a"
let vs_ia = create_vsymbol (id_fresh "i") (ty_var tv_a)
let vs_ja = create_vsymbol (id_fresh "j") (ty_var tv_a)
let vs_ka = create_vsymbol (id_fresh "k") (ty_var tv_a)
let vs_la = create_vsymbol (id_fresh "l") (ty_var tv_a)
let vs_ma = create_vsymbol (id_fresh "m") (ty_var tv_a)

let tv_c = tv_of_string "c"
let vs_uc = create_vsymbol (id_fresh "u") (ty_var tv_c)
let vs_vc = create_vsymbol (id_fresh "v") (ty_var tv_c)

let expr1 =
  !hs_alloc -- ty_int -+ t_nat_const 1 -* lam [Pr vs_pi] (
    !hs_loop -- ty_int -+ t_var vs_pi -* !hs_out -+
                              t_nat_const 3 -+ t_nat_const 0 -+ t_nat_const 5
    << def hs_loop [vs_pi] [Pt tv_a; Pv vs_ia; Pc (hs_ret,[vs_pi],[Pv vs_ja]);
                                                Pv vs_ka; Pv vs_la; Pv vs_ma]
          (cut (t_and (t_neq (t_var vs_ia) (t_var vs_ka))
                   (t_neq (t_var vs_pi) (t_nat_const 9)))
          (Ebox (!hs_if -+ (t_if (t_equ (t_var vs_ia) (t_var vs_la))
                                t_bool_true t_bool_false) -*
             lam [] (!hs_assign -- ty_int -& vs_pi -+ t_nat_const 2 -*
                lam [] (cut (t_neq (t_var vs_qi) (t_var vs_pi))
                  (!hs_loop -- ty_var tv_a -+ t_var vs_ia -* !hs_ret_
                    -+ t_var vs_la -+ t_var vs_ma -+ t_var vs_ka))
                <> [vs_qi, t_var vs_pi]) -*
             lam [] (!hs_ret_ -+ t_var vs_ia)))
        >> def hs_ret_ [vs_pi] [Pv vs_ja]
          (cut (t_and (t_equ (t_var vs_ma) (t_var vs_ja))
                       (t_equ (t_nat_const 55) (t_var vs_pi)))
                                   (Ebox (!hs_ret -+ t_var vs_ja))))
    >> def hs_out [vs_pi] [Pv vs_ii]
      (cut (t_and (t_equ (t_var vs_ii) (t_nat_const 42))
                   (t_equ (t_var vs_pi) (t_nat_const 37))) (Ebox !hs_halt)))
  >> def hs_assign [] [Pt tv_c; Pr vs_uc; Pv vs_vc; Pc (hs_ret,[vs_uc],[])]
      (Eany >> def hs_ret [vs_uc] [] (cut (t_equ (t_var vs_uc) (t_var vs_vc))
                                              (Ebox (!hs_ret))))
  >> def hs_alloc [] [Pt tv_c; Pv vs_vc; Pc (hs_ret,[],[Pr vs_uc])]
      (Eany >> def hs_ret [] [Pr vs_uc] (cut (t_equ (t_var vs_uc) (t_var vs_vc))
                                              (Ebox (!hs_ret -& vs_uc))))
  >> def hs_if [] [Pv vs_bb; Pc (hs_then,[],[]); Pc (hs_else,[],[])]
      (Eany >> def hs_then [] [] (cut (t_equ (t_var vs_bb) t_bool_true) (Ebox !hs_then))
            >> def hs_else [] [] (cut (t_equ (t_var vs_bb) t_bool_false) (Ebox !hs_else)))
  >> def hs_fail [] [] (cut t_false Eany)
  >> def hs_halt [] [] (Ewox Eany)

let expr2 =
  !hs_alloc -- ty_int -+ t_nat_const 1 -* lam [Pr vs_qi] (
    !hs_loop -& vs_qi -- ty_int -+ t_var vs_qi -*
                          lam [Pv vs_ji] (!hs_out -& vs_qi -+ t_var vs_ji) -+
                              t_nat_const 3 -+ t_nat_const 0 -+ t_nat_const 5)
  << def hs_loop [] [Pr vs_pi; Pt tv_a; Pv vs_ia; Pc (hs_ret,[vs_pi],[Pv vs_ja]);
                                              Pv vs_ka; Pv vs_la; Pv vs_ma]
        (cut (t_and (t_neq (t_var vs_ia) (t_var vs_ka))
                  (t_neq (t_var vs_pi) (t_nat_const 9)))
        (Ebox (!hs_if -+ (t_if (t_equ (t_var vs_ia) (t_var vs_la))
                              t_bool_true t_bool_false) -*
            lam [] (!hs_assign -- ty_int -& vs_pi -+ t_nat_const 2 -*
              lam [] (cut (t_neq (t_var vs_qi) (t_var vs_pi))
                (!hs_loop -& vs_pi -- ty_var tv_a -+ t_var vs_ia -* !hs_ret_
                  -+ t_var vs_la -+ t_var vs_ma -+ t_var vs_ka))
              <> [vs_qi, t_var vs_pi]) -*
            lam [] (!hs_ret_ -+ t_var vs_ia)))
      >> def hs_ret_ [vs_pi] [Pv vs_ja]
        (cut (t_and (t_equ (t_var vs_ma) (t_var vs_ja))
                      (t_equ (t_nat_const 55) (t_var vs_pi)))
                                  (Ebox (!hs_ret -+ t_var vs_ja))))
  >> def hs_out [] [Pr vs_pi; Pv vs_ii]
      (cut (t_and (t_equ (t_var vs_ii) (t_nat_const 42))
                   (t_equ (t_var vs_pi) (t_nat_const 37))) (Ebox !hs_halt))
  >> def hs_assign [] [Pt tv_c; Pr vs_uc; Pv vs_vc; Pc (hs_ret,[vs_uc],[])]
      (Eany >> def hs_ret [vs_uc] [] (cut (t_equ (t_var vs_uc) (t_var vs_vc))
                                              (Ebox (!hs_ret))))
  >> def hs_alloc [] [Pt tv_c; Pv vs_vc; Pc (hs_ret,[],[Pr vs_uc])]
      (Eany >> def hs_ret [] [Pr vs_uc] (cut (t_equ (t_var vs_uc) (t_var vs_vc))
                                              (Ebox (!hs_ret -& vs_uc))))
  >> def hs_if [] [Pv vs_bb; Pc (hs_then,[],[]); Pc (hs_else,[],[])]
      (Eany >> def hs_then [] [] (cut (t_equ (t_var vs_bb) t_bool_true) (Ebox !hs_then))
            >> def hs_else [] [] (cut (t_equ (t_var vs_bb) t_bool_false) (Ebox !hs_else)))
  >> def hs_fail [] [] (cut t_false Eany)
  >> def hs_halt [] [] (Ewox Eany)

(*
type env = {
  ps_int_le : lsymbol;
  ps_int_ge : lsymbol;
  ps_int_lt : lsymbol;
  ps_int_gt : lsymbol;
  fs_int_pl : lsymbol;
  fs_int_mn : lsymbol;
}

let mk_env {Theory.th_export = ns_int} = {
  ps_int_le = Theory.ns_find_ls ns_int [op_infix "<="];
  ps_int_ge = Theory.ns_find_ls ns_int [op_infix ">="];
  ps_int_lt = Theory.ns_find_ls ns_int [op_infix "<"];
  ps_int_gt = Theory.ns_find_ls ns_int [op_infix ">"];
  fs_int_pl = Theory.ns_find_ls ns_int [op_infix "+"];
  fs_int_mn = Theory.ns_find_ls ns_int [op_infix "-"];
}
*)

let mk_goal tuc s e =
  let prs = Decl.create_prsymbol (id_fresh ("vc_" ^ s)) in
  Theory.add_prop_decl tuc Decl.Pgoal prs (vc e)

let read_channel env path _file _c =
(*
  let ast = Coma_lexer.parse file c in
  Format.printf "@[%a@]@." (fun fmt l ->
    List.iter (fun d -> Coma_syntax.print_decl fmt d) l) ast;
*)
  let th_int = Env.read_theory env ["int"] "Int" in
  let tuc = Theory.create_theory ~path (id_fresh "Coma") in
  let tuc = Theory.use_export tuc Theory.bool_theory in
  let tuc = Theory.use_export tuc th_int in
  let tuc = mk_goal tuc "expr1" expr1 in
  let tuc = mk_goal tuc "expr2" expr2 in
  Mstr.singleton "Coma" (Theory.close_theory tuc)

let () = Env.register_format Env.base_language "coma" ["coma"] read_channel
  ~desc:"Continuation Machine language"
