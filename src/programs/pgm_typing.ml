(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-                                                   *)
(*    Francois Bobot                                                      *)
(*    Jean-Christophe Filliatre                                           *)
(*    Johannes Kanig                                                      *)
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
open Theory
open Denv
open Ptree
open Pgm_ttree

type error =
  | Message of string

exception Error of error

let error ?loc e = match loc with
  | None -> raise (Error e)
  | Some loc -> raise (Loc.Located (loc, Error e))

let errorm ?loc f =
  let buf = Buffer.create 512 in
  let fmt = Format.formatter_of_buffer buf in
  Format.kfprintf
    (fun _ ->
       Format.pp_print_flush fmt ();
       let s = Buffer.contents buf in
       Buffer.clear buf;
       error ?loc (Message s))
    fmt f

let report fmt = function
  | Message s ->
      fprintf fmt "%s" s

let id_result = "result"

(* environments *)

let dty_bool uc = Tyapp (ns_find_ts (get_namespace uc) ["bool"], [])
let dty_unit uc = Tyapp (ns_find_ts (get_namespace uc) ["unit"], [])
let dty_label uc = Tyapp (ns_find_ts (get_namespace uc) ["label"], [])
let ts_arrow uc = ns_find_ts (get_namespace uc) ["arrow"]

type denv = {
  uc   : theory_uc;
  denv : Typing.denv;
}

let create_denv uc = 
  { uc   = uc;
    denv = Typing.create_denv uc;
  }

let create_type_var loc =
  let tv = Ty.create_tvsymbol (id_user "a" loc) in
  Tyvar (create_ty_decl_var ~loc ~user:false tv)

let dcurrying uc tyl ty =
  let make_arrow_type ty1 ty2 = Tyapp (ts_arrow uc, [ty1; ty2]) in
  List.fold_right make_arrow_type tyl ty

let uncurrying uc ty =
  let rec uncurry acc ty = match ty.ty_node with
    | Ty.Tyapp (ts, [t1; t2]) when ts == ts_arrow uc -> uncurry (t1 :: acc) t2
    | _ -> List.rev acc, ty
  in
  uncurry [] ty

let expected_type e ty =
  if not (Denv.unify e.dexpr_type ty) then
    errorm ~loc:e.dexpr_loc 
      "this expression has type %a, but is expected to have type %a"
      print_dty e.dexpr_type print_dty ty

(* phase 1: typing programs (using destructive type inference) *)

let pure_type env = Typing.dty env.denv

let rec dpurify env = function
  | DTpure ty -> 
      ty
  | DTarrow (bl, c) -> 
      dcurrying env.uc (List.map (fun (_,ty) -> dpurify env ty) bl)
	(dpurify env c.dc_result_type)

let rec dtype_v env = function
  | Pgm_ptree.Tpure pt -> 
      DTpure (pure_type env pt)
  | Pgm_ptree.Tarrow (bl, c) -> 
      let env, bl = map_fold_left dbinder env bl in
      let c = dtype_c env c in
      DTarrow (bl, c) 

and dtype_c env c = 
  let ty = dtype_v env c.Pgm_ptree.pc_result_type in
  { dc_result_name = c.Pgm_ptree.pc_result_name.id;
    dc_result_type = ty;
    dc_effect      = List.map (fun x -> x.id) c.Pgm_ptree.pc_effect;
    dc_pre         = env.denv, c.Pgm_ptree.pc_pre;
    dc_post        =   
      let denv = Typing.add_var id_result (dpurify env ty) env.denv in
      denv, c.Pgm_ptree.pc_post;
  }

and dbinder env ({id=x; id_loc=loc}, v) =
  let v = match v with
    | Some v -> dtype_v env v 
    | None -> DTpure (create_type_var loc)
  in
  let ty = dpurify env v in
  let env = { env with denv = Typing.add_var x ty env.denv } in
  env, (x, v)

let rec dexpr env e = 
  let d, ty = expr_desc env e.Pgm_ptree.expr_loc e.Pgm_ptree.expr_desc in
  { dexpr_desc = d; dexpr_loc = e.Pgm_ptree.expr_loc;
    dexpr_denv = env.denv; dexpr_type = ty;  }

and expr_desc env loc = function
  | Pgm_ptree.Econstant (ConstInt _ as c) ->
      DEconstant c, Tyapp (Ty.ts_int, [])
  | Pgm_ptree.Econstant (ConstReal _ as c) ->
      DEconstant c, Tyapp (Ty.ts_real, [])
  | Pgm_ptree.Eident (Qident {id=x}) when Typing.mem_var x env.denv ->
      (* local variable *)
      let ty = Typing.find_var x env.denv in
      DElocal x, ty
  | Pgm_ptree.Eident p ->
      let s, tyl, ty = Typing.specialize_fsymbol p env.uc in
      DEglobal s, dcurrying env.uc tyl ty
  | Pgm_ptree.Eapply (e1, e2) ->
      let e1 = dexpr env e1 in
      let e2 = dexpr env e2 in
      begin match e1.dexpr_type with
	| Tyapp (ts, [ty2; ty]) when Ty.ts_equal ts (ts_arrow env.uc) ->
	    expected_type e2 ty2;
	    DEapply (e1, e2), ty
	| _ ->
	    errorm ~loc:e1.dexpr_loc "this expression is not a function"
      end
  | Pgm_ptree.Efun (bl, t) ->
      let env, bl = map_fold_left dbinder env bl in
      let (_,e,_) as t = dtriple env t in
      let tyl = List.map (fun (x,_) -> Typing.find_var x env.denv) bl in
      let ty = dcurrying env.uc tyl e.dexpr_type in
      DEfun (bl, t), ty
  | Pgm_ptree.Elet ({id=x}, e1, e2) ->
      let e1 = dexpr env e1 in
      let ty1 = e1.dexpr_type in
      let env = { env with denv = Typing.add_var x ty1 env.denv } in
      let e2 = dexpr env e2 in
      DElet (x, e1, e2), e2.dexpr_type
  | Pgm_ptree.Eletrec _ (*(id, bl, v, p, e, q)*) ->
      assert false (*TODO*)

  | Pgm_ptree.Esequence (e1, e2) ->
      let e1 = dexpr env e1 in
      expected_type e1 (dty_unit env.uc);
      let e2 = dexpr env e2 in
      DEsequence (e1, e2), e2.dexpr_type
  | Pgm_ptree.Eif (e1, e2, e3) ->
      let e1 = dexpr env e1 in
      expected_type e1 (dty_bool env.uc);
      let e2 = dexpr env e2 in
      let e3 = dexpr env e3 in
      expected_type e3 e2.dexpr_type;
      DEif (e1, e2, e3), e2.dexpr_type
  | Pgm_ptree.Ewhile (e1, a, e2) ->
      let e1 = dexpr env e1 in
      expected_type e1 (dty_bool env.uc);
      let e2 = dexpr env e2 in
      expected_type e2 (dty_unit env.uc);
      DEwhile (e1, a, e2), (dty_unit env.uc)
  | Pgm_ptree.Elazy (op, e1, e2) ->
      let e1 = dexpr env e1 in
      expected_type e1 (dty_bool env.uc);
      let e2 = dexpr env e2 in
      expected_type e2 (dty_bool env.uc);
      DElazy (op, e1, e2), (dty_bool env.uc)
  | Pgm_ptree.Ematch (_el, _bl) ->
      assert false (*TODO*)
  | Pgm_ptree.Eskip ->
      DEskip, (dty_unit env.uc)
  | Pgm_ptree.Eabsurd ->
      DEabsurd, create_type_var loc

  | Pgm_ptree.Eassert (k, le) ->
      DEassert (k, le), (dty_unit env.uc) 
  | Pgm_ptree.Eghost e1 ->
      let e1 = dexpr env e1 in
      DEghost e1, e1.dexpr_type
  | Pgm_ptree.Elabel ({id=l}, e1) ->
      let ty = dty_label env.uc in
      let env = { env with denv = Typing.add_var l ty env.denv } in
      let e1 = dexpr env e1 in
      DElabel (l, e1), e1.dexpr_type
  | Pgm_ptree.Ecast (e1, ty) ->
      let e1 = dexpr env e1 in
      let ty = pure_type env ty in
      expected_type e1 ty;
      e1.dexpr_desc, ty

and dtriple env (p, e, q) =     
  let p = env.denv, p in
  let e = dexpr env e in
  let ty = e.dexpr_type in
  let denvq = Typing.add_var id_result ty env.denv in
  let q = denvq, q in
  (p, e, q)

(* phase 2: typing annotations *)

let currying uc tyl ty =
  let make_arrow_type ty1 ty2 = Ty.ty_app (ts_arrow uc) [ty1; ty2] in
  List.fold_right make_arrow_type tyl ty

let purify uc = function
  | Tpure ty -> 
      ty
  | Tarrow (bl, c) -> 
      currying uc (List.map (fun (v,_) -> v.vs_ty) bl)
	c.c_result_name.vs_ty

let rec type_v uc env = function
  | DTpure ty -> 
      Tpure (Denv.ty_of_dty ty)
  | DTarrow (bl, c) -> 
      let env, bl = map_fold_left (binder uc) env bl in
      Tarrow (bl, type_c uc env c)

and type_c uc env c = 
  let tyv = type_v uc env c.dc_result_type in
  let ty = purify uc tyv in
  let v = create_vsymbol (id_fresh c.dc_result_name) ty in
  { c_result_name = v;
    c_result_type = tyv;
    c_effect      = []; (* TODO *)
    c_pre         = 
      (let denv, l = c.dc_pre in Typing.type_fmla denv env l);
    c_post        =
	  let denv, l = c.dc_post in 
	  let v_result = create_vsymbol (id_fresh id_result) ty in
	  let env = Mstr.add id_result v_result env in
 	  Typing.type_fmla denv env l;
  }
    
and binder uc env (x, tyv) = 
  let tyv = type_v uc env tyv in
  let v = create_vsymbol (id_fresh x) (purify uc tyv) in
  let env = Mstr.add x v env in
  env, (v, tyv)

let rec expr uc env e =
  let d = expr_desc uc env e.dexpr_denv e.dexpr_desc in
  let ty = Denv.ty_of_dty e.dexpr_type in
  { expr_desc = d; expr_type = ty; expr_loc = e.dexpr_loc }

and expr_desc uc env denv = function
  | DEconstant c ->
      Econstant c
  | DElocal x ->
      Elocal (Mstr.find x env)
  | DEglobal ls ->
      Eglobal ls
  | DEapply (e1, e2) ->
      Eapply (expr uc env e1, expr uc env e2)
  | DEfun (bl, e1) ->
      let env, bl = map_fold_left (binder uc) env bl in
      Efun (bl, triple uc env e1)
  | DElet (x, e1, e2) ->
      let e1 = expr uc env e1 in
      let v = create_vsymbol (id_fresh x) e1.expr_type in
      let env = Mstr.add x v env in
      Elet (v, e1, expr uc env e2)
  | DEletrec _ ->
      assert false (*TODO*)

  | DEsequence (e1, e2) ->
      Esequence (expr uc env e1, expr uc env e2)
  | DEif (e1, e2, e3) ->
      Eif (expr uc env e1, expr uc env e2, expr uc env e3)
  | DEwhile (e1, la, e2) ->
      let la = 
	{ loop_invariant = 
	    option_map (Typing.type_fmla denv env) la.Pgm_ptree.loop_invariant;
	  loop_variant   = 
	    option_map (Typing.type_term denv env) la.Pgm_ptree.loop_variant; }
      in
      Ewhile (expr uc env e1, la, expr uc env e2)
  | DElazy (op, e1, e2) ->
      Elazy (op, expr uc env e1, expr uc env e2)
  | DEskip ->
      Eskip
  | DEabsurd ->
      Eabsurd

  | DEassert (k, f) ->
      let f = Typing.type_fmla denv env f in
      Eassert (k, f)
  | DEghost e1 -> 
      Eghost (expr uc env e1)
  | DElabel (s, e1) ->
      let ty = Denv.ty_of_dty (Typing.find_var s e1.dexpr_denv) in
      let v = create_vsymbol (id_fresh s) ty in
      let env = Mstr.add s v env in 
      Elabel (s, expr uc env e1)

and triple uc env ((denvp, p), e, (denvq, q)) =
  let p = Typing.type_fmla denvp env p in
  let e = expr uc env e in
  let v_result = create_vsymbol (id_fresh id_result) e.expr_type in
  let envq = Mstr.add id_result v_result env in
  let q = Typing.type_fmla denvq envq q in
  (p, e, q)

let type_expr uc e =
  let denv = create_denv uc in
  let e = dexpr denv e in
  expr uc Mstr.empty e

let file env uc dl =
  let uc, dl =
    List.fold_left
      (fun (uc, acc) d -> match d with
	 | Pgm_ptree.Dlogic dl -> 
	     List.fold_left (Typing.add_decl env Mnm.empty) uc dl, acc
	 | Pgm_ptree.Dlet (id, e) -> 
	     let e = type_expr uc e in
	     let tyl, ty = uncurrying uc e.expr_type in
	     let ls = create_lsymbol (id_user id.id id.id_loc) tyl (Some ty) in
	     uc, Dlet (ls, e) :: acc
	 | Pgm_ptree.Dletrec _ -> 
	     assert false (*TODO*)
	 | Pgm_ptree.Dparam (id, tyv) ->
	     let denv = create_denv uc in
	     let tyv = dtype_v denv tyv in
	     let tyv = type_v uc Mstr.empty tyv in
	     let tyl, ty = uncurrying uc (purify uc tyv) in
	     let ls = create_lsymbol (id_user id.id id.id_loc) tyl (Some ty) in
	     uc, Dparam (ls, tyv) :: acc
      )
      (uc, []) dl
  in
  uc, List.rev dl

(*
Local Variables: 
compile-command: "unset LANG; make -C ../.. testl"
End: 
*)
