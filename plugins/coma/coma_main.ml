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
  hs_eff  : vsymbol list;
  hs_sig  : signature;
}

and signature =
  | SGend
  | SGtyp of tvsymbol * signature
  | SGval of vsymbol * signature
  | SGref of vsymbol * signature
  | SGcnt of hsymbol * signature

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

let create_hsymbol id eff sg = {
  hs_name = id_register id;
  hs_eff  = eff;
  hs_sig  = sg;
}

type expr =
  | Esym of hsymbol
  | Etyp of expr * ty
  | Eval of expr * term
  | Eref of expr * vsymbol
  | Ecnt of expr * expr
  | Elam of signature * expr
  | Edef of expr * hsymbol * expr
  | Easr of term * expr
  | Ebbx of expr
  | Ewbx of expr
  | Ehol

type stack =
  | STend
  | STeff of vsymbol * term * stack
  | STtyp of ty * stack
  | STval of term * stack
  | STref of term * stack
  | STcnt of closure * stack

and closure = stack -> bool -> term

let rec invert acc = function
  | STtyp (t,st) -> invert (STtyp (t,acc)) st
  | STeff (v,t,st) -> invert (STeff (v,t,acc)) st
  | STval (t,st) -> invert (STval (t,acc)) st
  | STref (t,st) -> invert (STref (t,acc)) st
  | STcnt (d,st) -> invert (STcnt (d,acc)) st
  | STend -> acc

let get_ref t = match t.t_node with
  | Tvar v -> v | _ -> assert false

(*
let t_and_simp = t_and
let t_and_asym_simp = t_and_asym
let t_implies_simp = t_implies
let t_forall_close_simp = t_forall_close
*)

let rec fail tsb sbs sg st safe = match sg,st with
  | SGtyp (v,sg), STtyp (t,st) ->
      fail (Mtv.add v t tsb) sbs sg st safe
  | sg, STeff (v,t,st)
  | SGval (v,sg), STval (t,st)
  | SGref (v,sg), STref (t,st) ->
      fail tsb (Mvs.add v t sbs) sg st safe
  | SGcnt (h,sg), STcnt (d,st) ->
      let vcd _ _ _ st = d st true in
      let lhs = havoc tsb sbs Mhs.empty h vcd safe in
      t_and_simp lhs (fail tsb sbs sg st safe)
  | SGend, STend ->
      if safe then t_false else t_true
  | _ -> assert false

and havoc tsb sbs ctx h fn safe =
  let rec link tsb sbs ctx vl st = function
    | SGtyp (v,sg) ->
        let t = ty_var (create_tvsymbol (id_clone v.tv_name)) in
        link (Mtv.add v t tsb) sbs ctx vl (STtyp (t,st)) sg
    | SGval (v,sg) ->
        let ty = ty_inst tsb v.vs_ty in
        let u = create_vsymbol (id_clone v.vs_name) ty in
        let t = t_var u in
        link tsb (Mvs.add v t sbs) ctx (u::vl) (STval (t,st)) sg
    | SGref (v,sg) ->
        let ty = ty_inst tsb v.vs_ty in
        let u = create_vsymbol (id_clone v.vs_name) ty in
        let t = t_var u in
        link tsb (Mvs.add v t sbs) ctx (u::vl) (STref (t,st)) sg
    | SGcnt (h,sg) ->
        let f st safe0 = fail tsb sbs h.hs_sig st (safe && safe0) in
        link tsb sbs (Mhs.add h f ctx) vl (STcnt (f,st)) sg
    | SGend ->
        let f = fn tsb sbs ctx (invert STend st) in
        t_forall_close_simp (List.rev vl) [] f in
  let rec prwr sbs vl st = function
    | p::pl ->
        let q = get_ref (Mvs.find p sbs) in
        let r = create_vsymbol (id_clone q.vs_name) q.vs_ty in
        let t = t_var r in
        prwr (Mvs.add p t sbs) (r::vl) (STeff (q,t,st)) pl
    | [] ->
        link tsb sbs ctx vl st h.hs_sig in
  prwr sbs [] STend h.hs_eff

let rec consume fn tsb sbs ctx full prot sg st = match sg,st with
  | SGtyp (v,sg), STtyp (t,st) ->
      consume fn (Mtv.add v t tsb) sbs ctx full prot sg st
  | sg, STeff (v,t,st)
  | SGval (v,sg), STval (t,st)
  | SGref (v,sg), STref (t,st) ->
      consume fn tsb (Mvs.add v t sbs) ctx full prot sg st
  | SGcnt (h,sg), STcnt (d,st) ->
      let prot = if full then prot else Shs.add h prot in
      consume fn tsb sbs (Mhs.add h d ctx) full prot sg st
  | SGend, st ->
      fn tsb sbs ctx full prot st
  | _ -> assert false

let rec vc stack pp dd tsb sbs ctx full prot = function
  | Esym h ->
      let add st v = STeff (v, Mvs.find v sbs, st) in
      let stack = List.fold_left add stack h.hs_eff in
      Mhs.find h ctx stack (pp && (full || Shs.mem h prot))
  | Etyp (e,t) ->
      let stack = STtyp (ty_inst tsb t, stack) in
      vc stack pp dd tsb sbs ctx full prot e
  | Eval (e,t) ->
      let stack = STval (t_ty_subst tsb sbs t, stack) in
      vc stack pp dd tsb sbs ctx full prot e
  | Eref (e,r) ->
      let stack = STref (t_ty_subst tsb sbs (t_var r), stack) in
      vc stack pp dd tsb sbs ctx full prot e
  | Ecnt (e,d) ->
      let vcd stack safe =
        let prot = if safe then prot else Shs.empty in
        vc stack pp dd tsb sbs ctx (safe && full) prot d in
      vc (STcnt (vcd, stack)) pp dd tsb sbs ctx full prot e
  | Elam (sg,e) ->
      let vce tsb sbs ctx full prot stack =
        assert (stack = STend);
        let lhs = vc STend pp dd tsb sbs ctx full prot e in
        let rec prot acc = function
          | SGtyp (_,sg) | SGval (_,sg) | SGref (_,sg) -> prot acc sg
          | SGcnt (h,sg) -> prot (Shs.add h acc) sg | SGend -> acc in
        let prot = prot Shs.empty sg in
        let rhs = vc STend (not pp) (not dd) tsb sbs ctx false prot e in
        t_and_simp lhs rhs in
      consume vce tsb sbs ctx full prot sg stack
  | Edef (e,h,d) ->
      assert (stack = STend);
      let vcd stack safe =
        let full = safe && full in
        let prot = if safe then prot else Shs.empty in
        let vcd tsb sbs ctx full prot stack =
          assert (stack = STend);
          let ctx = Mhs.add h (fail tsb sbs h.hs_sig) ctx in
          vc STend true false tsb sbs ctx full prot d in
        consume vcd tsb sbs ctx full prot h.hs_sig stack in
      let ctx = Mhs.add h vcd ctx in
      let lhs = vc stack pp dd tsb sbs ctx full prot e in
      let vcd tsb sbs ctx _ =
        vc STend false pp tsb sbs ctx full prot d in
      t_and_simp lhs (havoc tsb sbs ctx h vcd true)
  | Easr (f,e) ->
      assert (stack = STend);
      let f = t_ty_subst tsb sbs f in
      (if pp && full then t_and_asym_simp else t_implies_simp)
        f (vc stack pp dd tsb sbs ctx full prot e)
  | Ebbx e -> vc stack dd dd tsb sbs ctx full prot e
  | Ewbx e -> vc stack pp pp tsb sbs ctx full prot e
  | Ehol -> t_true

let vc e = vc STend true true Mtv.empty Mvs.empty Mhs.empty true Shs.empty e

let hs_halt = create_hsymbol (id_fresh "halt") [] SGend
let hs_fail = create_hsymbol (id_fresh "fail") [] SGend
let hs_then = create_hsymbol (id_fresh "then") [] SGend
let hs_else = create_hsymbol (id_fresh "else") [] SGend
let hs_the0 = create_hsymbol (id_fresh "the0") [] SGend
let hs_els0 = create_hsymbol (id_fresh "els0") [] SGend

let vs_ii = create_vsymbol (id_fresh "i") ty_int
let vs_ji = create_vsymbol (id_fresh "j") ty_int
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

let hs_if = create_hsymbol (id_fresh "if") []
  (SGval (vs_bb, SGcnt (hs_then, SGcnt (hs_else, SGend))))

let hs_break = create_hsymbol (id_fresh "break") [vs_pi] (SGval (vs_ii, SGend))

let hs_loop_ret = create_hsymbol (id_fresh "ret") [vs_pi] (SGval (vs_ia, SGend))
let hs_loop_re0 = create_hsymbol (id_fresh "re0") [vs_pi] (SGval (vs_ja, SGend))
let hs_loop = create_hsymbol (id_fresh "loop") [vs_pi]
  (SGtyp (tv_a, SGval (vs_ia, SGcnt (hs_loop_ret,
    SGval (vs_ka, SGval (vs_la, SGval (vs_ma, SGend)))))))

let hs_alloc_ret = create_hsymbol (id_fresh "alloc_ret") [] (SGref (vs_vc, SGend))
let hs_alloc_re0 = create_hsymbol (id_fresh "alloc_re0") [] (SGref (vs_uc, SGend))
let hs_alloc = create_hsymbol (id_fresh "alloc") []
  (SGtyp (tv_c, SGval (vs_vc, SGcnt (hs_alloc_ret, SGend))))

let hs_assign_ret = create_hsymbol (id_fresh "assign_ret") [vs_uc] SGend
let hs_assign_re0 = create_hsymbol (id_fresh "assign_re0") [vs_uc] SGend
let hs_assign = create_hsymbol (id_fresh "assign") []
  (SGtyp (tv_c, SGref (vs_uc, SGval (vs_vc, SGcnt (hs_assign_ret, SGend)))))


let expr1 =
  Edef (Edef (Edef (Edef (Edef (

    Ecnt (Eval (Etyp (Esym hs_alloc, ty_int), t_nat_const 17),
    Elam (SGref (vs_pi, SGend), Edef (Edef (Eval (Eval (Eval (
        Ecnt (Eval (Etyp (Esym hs_loop, ty_int), t_var vs_pi), Esym hs_break),
          t_nat_const 3), t_nat_const 0), t_nat_const 5)
    , hs_loop, Edef( Easr (t_and (t_neq (t_var vs_ia) (t_var vs_ka))
                                 (t_neq (t_var vs_pi) (t_nat_const 9)),
        Ebbx (Ecnt (Ecnt (Eval (Esym hs_if,
            t_if (t_equ (t_var vs_ia) (t_var vs_la)) t_bool_true t_bool_false),
          Ecnt (Eval (Eref (Etyp (Esym hs_assign, ty_int), vs_pi), t_nat_const 2),
          Elam (SGend, Eval (Eval (Eval (
            Ecnt (Eval (Etyp (Esym hs_loop, ty_var tv_a), t_var vs_ia), Esym hs_loop_re0),
              t_var vs_la), t_var vs_ma), t_var vs_ka)))),
          Eval (Esym hs_loop_re0, t_var vs_ia))))
        , hs_loop_re0, Easr (t_and (t_equ (t_var vs_ma) (t_var vs_ja))
                                   (t_equ (t_nat_const 55) (t_var vs_pi)),
            Ebbx (Eval (Esym hs_loop_ret, t_var vs_ja)))))
    , hs_break, Easr (
        t_and (t_equ (t_var vs_ii) (t_nat_const 42))
              (t_equ (t_var vs_pi) (t_nat_const 37)), Ebbx (Esym hs_halt)))))

  , hs_if, Edef (Edef (Ehol, hs_the0, Easr (t_equ (t_var vs_bb) t_bool_true, Ebbx (Esym hs_then))),
                             hs_els0, Easr (t_equ (t_var vs_bb) t_bool_false, Ebbx (Esym hs_else))))
  , hs_assign, Edef (Ehol, hs_assign_re0, Easr (t_equ (t_var vs_uc) (t_var vs_vc),
                Ebbx (Esym hs_assign_ret))))
  , hs_alloc, Edef (Ehol, hs_alloc_re0, Easr (t_equ (t_var vs_uc) (t_var vs_vc),
                Ebbx (Eref (Esym hs_alloc_ret, vs_uc)))))
  , hs_halt, Ehol)
  , hs_fail, Easr (t_false, Ehol))

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
  let vcf = vc e in
(*   Format.printf "@[%a@]@." Pretty.print_term vcf; *)
  Theory.add_prop_decl tuc Decl.Pgoal prs vcf

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
  let tuc = mk_goal tuc "e1" expr1 in
  Mstr.singleton "Coma" (Theory.close_theory tuc)

let () = Env.register_format Env.base_language "coma" ["coma"] read_channel
  ~desc:"Continuation Machine language"
