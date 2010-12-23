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
open Pp
open Util
open Ident
open Ty
open Term
open Theory
open Denv
open Ptree
open Pgm_ttree
open Pgm_types
open Pgm_types.T
open Pgm_module

let debug = Debug.register_flag "program_typing"

exception Message of string

let error ?loc e = match loc with
  | None -> raise e
  | Some loc -> raise (Loc.Located (loc, e))

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

let () = Exn_printer.register (fun fmt e -> match e with
  | Message s -> fprintf fmt "%s" s
  | _ -> raise e)

let id_result = "result"

(* phase 1: typing programs (using destructive type inference) **************)

let dty_app (ts, tyl) = assert (ts.ts_def = None); Tyapp (ts, tyl)

let find_ts uc s = ns_find_ts (get_namespace (theory_uc uc)) [s]
let find_ls uc s = ns_find_ls (get_namespace (theory_uc uc)) [s]

(* TODO: improve efficiency *)
let dty_bool uc = dty_app (find_ts uc "bool", [])
let dty_int _uc = dty_app (Ty.ts_int, [])
let dty_unit _uc = dty_app (ts_tuple 0, [])
let dty_label uc = dty_app (find_ts uc "label", [])

(* note: local variables are simultaneously in locals (to type programs)
   and in denv (to type logic elements) *)
type denv = {
  uc    : uc;
  locals: Denv.dty Mstr.t;
  denv  : Typing.denv;
}

let create_denv uc =
  { uc = uc;
    locals = Mstr.empty;
    denv = Typing.create_denv (theory_uc uc); }

let specialize_effect e =
  let reference r acc = match r with
    | R.Rlocal v -> DRlocal v.pv_name.id_string :: acc
    | R.Rglobal l -> DRglobal l :: acc
  in
  { de_reads  = Sref.fold reference e.E.reads  [];
    de_writes = Sref.fold reference e.E.writes [];
    de_raises = Sexn.elements e.E.raises; }

let specialize_post ~loc htv ((v, f), ql) =
  assert (v.vs_name.id_string = "result"); (* TODO *)
  let specialize_exn (l, (v, f)) =
    assert
      (match v with Some v -> v.vs_name.id_string = "result" | None -> true);
    let ty = option_map (fun v -> Denv.specialize_ty ~loc htv v.vs_ty) v in
    (l, (ty, specialize_fmla ~loc htv f))
  in
  let ty = Denv.specialize_ty ~loc htv v.vs_ty in
  let f = specialize_fmla ~loc htv f in
  (ty, f), List.map specialize_exn ql

let rec loc_of_id id = match id.id_origin with
  | User loc -> loc
  | Derived id -> loc_of_id id
  | _ -> assert false

let loc_of_ls ls = match ls.ls_name.id_origin with
  | User loc -> Some loc
  | _ -> None (* FIXME: loc for recursive functions *)

let dmodel_type = function
  | Tyapp (ts, tyl) as ty ->
      let mt = get_mtsymbol ts in
      begin match mt.mt_model with
	| None -> 
	    ty
	| Some ty ->
	    let h = Htv.create 17 in
	    List.iter2 (Htv.add h) mt.mt_args tyl;
	    let rec inst ty = match ty.ty_node with
	      | Ty.Tyvar tv -> Htv.find h tv
	      | Ty.Tyapp (ts, tyl) -> Denv.Tyapp (ts, List.map inst tyl)
	    in
	    inst ty
      end
  | Tyvar _ as ty -> 
      ty

let dpurify ty = try dmodel_type ty with NotMutable -> ty

let dcurrying tyl ty =
  let make_arrow_type ty1 ty2 = dty_app (ts_arrow, [ty1; ty2]) in
  List.fold_right make_arrow_type tyl ty

let rec dpurify_type_v ?(logic=false) = function
  | DTpure ty ->
      if logic then dpurify ty else ty
  | DTarrow (bl, c) ->
      dcurrying (List.map (fun (_,ty,_) -> if logic then dpurify ty else ty) bl)
	(dpurify_type_v c.dc_result_type)

let rec specialize_type_v ~loc htv = function
  | Tpure ty ->
      DTpure (Denv.specialize_ty ~loc htv ty)
  | Tarrow (bl, c) ->
      DTarrow (List.map (specialize_binder ~loc htv) bl,
	       specialize_type_c ~loc htv c)

and specialize_type_c ~loc htv c =
  { dc_result_type = specialize_type_v ~loc htv c.c_result_type;
    dc_effect      = specialize_effect c.c_effect;
    dc_pre         = specialize_fmla ~loc htv c.c_pre;
    dc_post        = specialize_post ~loc htv c.c_post; }

and specialize_binder ~loc htv v =
  let id = { id = v.pv_name.id_string;
             id_lab = v.pv_name.id_label;
             id_loc = loc } in
  let v = specialize_type_v ~loc htv v.pv_tv in
  id, dpurify_type_v v, v

let specialize_global loc x uc =
  let p = ns_find_pr (namespace uc) x in
  p, specialize_type_v ~loc (Htv.create 17) p.p_tv

let dot fmt () = pp_print_string fmt "."
let print_qualids = print_list dot pp_print_string
let print_qualid fmt q = 
  print_list dot pp_print_string fmt (Typing.string_list_of_qualid [] q)

let specialize_exception loc x uc =
  let s = 
    try ns_find_ex (namespace uc) x
    with Not_found -> errorm ~loc "@[unbound exception %a@]" print_qualids x
  in
  match Denv.specialize_lsymbol ~loc s with
    | tyl, Some ty -> s, tyl, ty
    | _, None -> assert false

let create_type_var loc =
  let tv = Ty.create_tvsymbol (id_user "a" loc) in
  Tyvar (create_ty_decl_var ~loc ~user:false tv)

let add_pure_var id ty env = match ty with
  | Tyapp (ts, _) when Ty.ts_equal ts ts_arrow -> env.denv
  | _ -> Typing.add_var id ty env.denv

let uncurrying ty =
  let rec uncurry acc ty = match ty.ty_node with
    | Ty.Tyapp (ts, [t1; t2]) when ts_equal ts ts_arrow ->
	uncurry (t1 :: acc) t2
    | _ ->
	List.rev acc, ty
  in
  uncurry [] ty

let expected_type e ty =
  if not (Denv.unify e.dexpr_type ty) then
    errorm ~loc:e.dexpr_loc
      "this expression has type %a, but is expected to have type %a"
      print_dty e.dexpr_type print_dty ty

let pure_type env = Typing.dty env.denv

let check_reference_type uc loc ty =
  let ty_ref = dty_app (find_ts uc "ref", [create_type_var loc]) in
  if not (Denv.unify ty ty_ref) then
    errorm ~loc "this expression has type %a, but is expected to be a reference"
      print_dty ty

let dreference env = function
  | Qident id when Typing.mem_var id.id env.denv ->
      (* local variable *)
      let ty = Typing.find_var id.id env.denv in
      check_reference_type env.uc id.id_loc ty;
      DRlocal id.id
  | qid ->
      let loc = Typing.qloc qid in
      let sl = Typing.string_list_of_qualid [] qid in
      let s, _ty = specialize_global loc sl env.uc in
      (* TODO check_reference_type env.uc loc ty; *)
      DRglobal s

let dexception env qid =
  let sl = Typing.string_list_of_qualid [] qid in
  let loc = Typing.qloc qid in
  let _, _, ty as r = specialize_exception loc sl env.uc in
  let ty_exn = dty_app (find_ts env.uc "exn", []) in
  if not (Denv.unify ty ty_exn) then
    errorm ~loc
      "this expression has type %a, but is expected to be an exception"
      print_dty ty;
  r

let deffect env e =
  { de_reads  = List.map (dreference env) e.Pgm_ptree.pe_reads;
    de_writes = List.map (dreference env) e.Pgm_ptree.pe_writes;
    de_raises =
      List.map (fun id -> let ls,_,_ = dexception env id in ls)
	e.Pgm_ptree.pe_raises; }

let dterm env l = Typing.dterm ~localize:true env (Pgm_module.logic_lexpr l)
let dfmla env l = Typing.dfmla ~localize:true env (Pgm_module.logic_lexpr l)

let dpost env ty (q, ql) =
  let dexn (id, l) =
    let s, tyl, _ = dexception env id in
    let ty, denv = match tyl with
      | [] -> None, env.denv
      | [ty] -> Some ty, add_pure_var id_result ty env
      | _ -> assert false
    in
    s, (ty, dfmla denv l)
  in
  let denv = add_pure_var id_result ty env in
  (ty, dfmla denv q), List.map dexn ql

let add_local_top env x tyv =
  { env with locals = Mstr.add x tyv env.locals }

let add_local env x ty =
  { env with locals = Mstr.add x ty env.locals;
             denv = add_pure_var x (dpurify ty) env }

let rec dtype_v env = function
  | Pgm_ptree.Tpure pt ->
      DTpure (pure_type env pt)
  | Pgm_ptree.Tarrow (bl, c) ->
      let env, bl = map_fold_left dbinder env bl in
      let c = dtype_c env c in
      DTarrow (bl, c)

and dtype_c env c =
  let ty = dtype_v env c.Pgm_ptree.pc_result_type in
  { dc_result_type = ty;
    dc_effect      = deffect env c.Pgm_ptree.pc_effect;
    dc_pre         = dfmla env.denv c.Pgm_ptree.pc_pre;
    dc_post        = dpost env (dpurify_type_v ty) c.Pgm_ptree.pc_post;
  }

and dbinder env ({id=x; id_loc=loc} as id, v) =
  let v = match v with
    | Some v -> dtype_v env v
    | None -> DTpure (create_type_var loc)
  in
  let ty = dpurify_type_v v in
  add_local env x ty, (id, ty, v)

let rec add_local_pat env p = match p.dp_node with
  | Denv.Pwild -> env
  | Denv.Pvar x -> add_local env x.id p.dp_ty
  | Denv.Papp (_, pl) -> List.fold_left add_local_pat env pl
  | Denv.Pas (p, x) -> add_local_pat (add_local env x.id p.dp_ty) p
  | Denv.Por (p, q) -> add_local_pat (add_local_pat env p) q

let dvariant env (l, p) =
  let s, _ = Typing.specialize_psymbol p (theory_uc env.uc) in
  let loc = Typing.qloc p in
  begin match s.ls_args with
    | [t1; t2] when Ty.ty_equal t1 t2 ->
	()
    | _ ->
	errorm ~loc "predicate %s should be a binary relation"
	  s.ls_name.id_string
  end;
  dterm env.denv l, s

let dloop_annotation env a =
  { dloop_invariant = option_map (dfmla env.denv) a.Pgm_ptree.loop_invariant;
    dloop_variant   = option_map (dvariant env) a.Pgm_ptree.loop_variant; }

(* [dexpr] translates ptree into dexpr *)

let rec dexpr env e =
  let d, ty = dexpr_desc env e.Pgm_ptree.expr_loc e.Pgm_ptree.expr_desc in
  { dexpr_desc = d; dexpr_loc = e.Pgm_ptree.expr_loc;
    dexpr_denv = env.denv; dexpr_type = ty; }

and dexpr_desc env loc = function
  | Pgm_ptree.Econstant (ConstInt _ as c) ->
      DEconstant c, dty_app (Ty.ts_int, [])
  | Pgm_ptree.Econstant (ConstReal _ as c) ->
      DEconstant c, dty_app (Ty.ts_real, [])
  | Pgm_ptree.Eident (Qident {id=x}) when Mstr.mem x env.locals ->
      (* local variable *)
      let tyv = Mstr.find x env.locals in
      DElocal (x, tyv), dpurify tyv
  | Pgm_ptree.Eident p ->
      begin try
	(* global variable *)
	let x = Typing.string_list_of_qualid [] p in
	let s, tyv = specialize_global loc x env.uc in
	DEglobal (s, tyv), dpurify_type_v tyv
      with Not_found ->
	let s,tyl,ty = Typing.specialize_lsymbol p (theory_uc env.uc) in
	let ty = match ty with
          | Some ty -> ty
          | None -> dty_bool env.uc
	in
	DElogic s, dcurrying tyl ty
      end
  | Pgm_ptree.Eapply (e1, e2) ->
      let e1 = dexpr env e1 in
      let e2 = dexpr env e2 in
      let ty2 = create_type_var loc and ty = create_type_var loc in
      if not (Denv.unify e1.dexpr_type (dty_app (ts_arrow, [ty2; ty])))
      then
	errorm ~loc:e1.dexpr_loc "this expression is not a function";
      expected_type e2 ty2;
      DEapply (e1, e2), ty
  | Pgm_ptree.Efun (bl, t) ->
      let env, bl = map_fold_left dbinder env bl in
      let (_,e,_) as t = dtriple env t in
      let tyl = List.map (fun (_,ty,_) -> ty) bl in
      let ty = dcurrying tyl e.dexpr_type in
      DEfun (bl, t), ty
  | Pgm_ptree.Elet (x, e1, e2) ->
      let e1 = dexpr env e1 in
      let ty1 = e1.dexpr_type in
      let env = add_local env x.id ty1 in
      let e2 = dexpr env e2 in
      DElet (x, e1, e2), e2.dexpr_type
  | Pgm_ptree.Eletrec (dl, e1) ->
      let env, dl = dletrec env dl in
      let e1 = dexpr env e1 in
      DEletrec (dl, e1), e1.dexpr_type
  | Pgm_ptree.Etuple el ->
      let n = List.length el in
      let s = Typing.fs_tuple n in
      let tyl = List.map (fun _ -> create_type_var loc) el in
      let ty = dty_app (Typing.ts_tuple n, tyl) in
      let create d ty =
	{ dexpr_desc = d; dexpr_denv = env.denv;
	  dexpr_type = ty; dexpr_loc = loc }
      in
      let apply e1 e2 ty2 =
	let e2 = dexpr env e2 in
	assert (Denv.unify e2.dexpr_type ty2);
	let ty = create_type_var loc in
	assert (Denv.unify e1.dexpr_type
		  (dty_app (ts_arrow, [ty2; ty])));
	create (DEapply (e1, e2)) ty
      in
      let e = create (DElogic s) (dcurrying tyl ty) in
      let e = List.fold_left2 apply e el tyl in
      e.dexpr_desc, ty

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
  | Pgm_ptree.Eloop (a, e1) ->
      let e1 = dexpr env e1 in
      expected_type e1 (dty_unit env.uc);
      DEloop (dloop_annotation env a, e1), dty_unit env.uc
  | Pgm_ptree.Elazy (op, e1, e2) ->
      let e1 = dexpr env e1 in
      expected_type e1 (dty_bool env.uc);
      let e2 = dexpr env e2 in
      expected_type e2 (dty_bool env.uc);
      DElazy (op, e1, e2), dty_bool env.uc
  | Pgm_ptree.Ematch (e1, bl) ->
      let e1 = dexpr env e1 in
      let ty1 = e1.dexpr_type in
      let ty = create_type_var loc in (* the type of all branches *)
      let branch (p, e) =
	let denv, p = Typing.dpat_list env.denv ty1 p in
	let env = { env with denv = denv } in
	let env = add_local_pat env p in
	let e = dexpr env e in
	expected_type e ty;
	p, e
      in
      let bl = List.map branch bl in
      DEmatch (e1, bl), ty
  | Pgm_ptree.Eskip ->
      DElogic (fs_tuple 0), dty_unit env.uc
  | Pgm_ptree.Eabsurd ->
      DEabsurd, create_type_var loc
  | Pgm_ptree.Eraise (qid, e) ->
      let ls, tyl, _ = dexception env qid in
      let e = match e, tyl with
	| None, [] ->
	    None
	| Some _, [] ->
	    errorm ~loc "expection %a has no argument" print_qualid qid
	| None, [ty] ->
	    errorm ~loc "exception %a is expecting an argument of type %a"
	      print_qualid qid print_dty ty;
	| Some e, [ty] ->
	    let e = dexpr env e in
	    expected_type e ty;
	    Some e
	| _ ->
	    assert false
      in
      DEraise (ls, e), create_type_var loc
  | Pgm_ptree.Etry (e1, hl) ->
      let e1 = dexpr env e1 in
      let handler (id, x, h) =
	let ls, tyl, _ = dexception env id in
	let x, env = match x, tyl with
	  | Some _, [] ->
	      errorm ~loc "expection %a has no argument" print_qualid id
	  | None, [] ->
	      None, env
	  | None, [ty] ->
	      errorm ~loc "exception %a is expecting an argument of type %a"
		print_qualid id print_dty ty;
	  | Some x, [ty] ->
	      Some x.id, add_local env x.id ty
	  | _ ->
	      assert false
	in
	let h = dexpr env h in
	expected_type h e1.dexpr_type;
	(ls, x, h)
      in
      DEtry (e1, List.map handler hl), e1.dexpr_type
  | Pgm_ptree.Efor (x, e1, d, e2, inv, e3) ->
      let e1 = dexpr env e1 in
      expected_type e1 (dty_int env.uc);
      let e2 = dexpr env e2 in
      expected_type e2 (dty_int env.uc);
      let env = add_local env x.id (dty_int env.uc) in
      let inv = option_map (dfmla env.denv) inv in
      let e3 = dexpr env e3 in
      expected_type e3 (dty_unit env.uc);
      DEfor (x, e1, d, e2, inv, e3), dty_unit env.uc

  | Pgm_ptree.Eassert (k, le) ->
      DEassert (k, dfmla env.denv le), dty_unit env.uc
  | Pgm_ptree.Elabel ({id=s}, e1) ->
      if Typing.mem_var s env.denv then
	errorm ~loc "clash with previous label %s" s;
      let ty = dty_label env.uc in
      let env = { env with denv = add_pure_var s ty env } in
      let e1 = dexpr env e1 in
      DElabel (s, e1), e1.dexpr_type
  | Pgm_ptree.Ecast (e1, ty) ->
      let e1 = dexpr env e1 in
      let ty = pure_type env ty in
      expected_type e1 ty;
      e1.dexpr_desc, ty
  | Pgm_ptree.Eany c ->
      let c = dtype_c env c in
      DEany c, dpurify_type_v c.dc_result_type

and dletrec env dl =
  (* add all functions into environment *)
  let add_one env (id, bl, var, t) =
    let ty = create_type_var id.id_loc in
    let env = add_local_top env id.id ty in
    env, ((id, ty), bl, var, t)
  in
  let env, dl = map_fold_left add_one env dl in
  (* then type-check all of them and unify *)
  let type_one ((id, tyres), bl, v, t) =
    let env, bl = map_fold_left dbinder env bl in
    let v = option_map (dvariant env) v in
    let (_,e,_) as t = dtriple env t in
    let tyl = List.map (fun (_,ty,_) -> ty) bl in
    let ty = dcurrying tyl e.dexpr_type in
    if not (Denv.unify ty tyres) then
      errorm ~loc:id.id_loc
	"this expression has type %a, but is expected to have type %a"
	print_dty ty print_dty tyres;
    ((id, tyres), bl, v, t)
  in
  env, List.map type_one dl

and dtriple env (p, e, q) =
  let p = dfmla env.denv p in
  let e = dexpr env e in
  let ty = e.dexpr_type in
  let q = dpost env ty q in
  (p, e, q)

(* phase 2: remove destructive types and type annotations *****************)

let create_ivsymbol id ty = 
  let vs = create_vsymbol id ty in
  let ty' = purify ty in
  if ty_equal ty ty' then { i_pgm   = vs; i_logic = vs }
  else { i_pgm = vs; i_logic = create_vsymbol id ty'; }

let iadd_local env x ty =
  let v = create_ivsymbol (id_user x.id x.id_loc) ty in 
  let env = Mstr.add x.id v env in
  env, v
  
let ireference env = function
  | DRlocal x -> IRlocal (Mstr.find x env)
  | DRglobal ls -> IRglobal ls

let ieffect env e = {
  ie_reads  = List.map (ireference env) e.de_reads;
  ie_writes = List.map (ireference env) e.de_writes;
  ie_raises = e.de_raises;
}

let lenv = Mstr.map (fun x -> x.i_logic)

let pre env = Denv.fmla (lenv env) 

let post env ((ty, f), ql) =
  let env = lenv env in
  let exn (ls, (ty, f)) =
    let v, env = match ty with
      | None ->
	  None, env
      | Some ty ->
	  let ty = Denv.ty_of_dty ty in
	  let v_result = create_vsymbol (id_fresh id_result) ty in
	  Some v_result, Mstr.add id_result v_result env
    in
    (ls, (v, Denv.fmla env f))
  in
  let ty = Denv.ty_of_dty ty in
  let v_result = create_vsymbol (id_fresh id_result) ty in
  let env = Mstr.add id_result v_result env in
  (v_result, Denv.fmla env f), List.map exn ql

let variant loc env (t, ps) =
  let t = Denv.term env t in
  match ps.ls_args with
    | [t1; _] when Ty.ty_equal t1 t.t_ty ->
	t, ps
    | [t1; _] ->
	errorm ~loc "@[variant has type %a, but is expected to have type %a@]"
	  Pretty.print_ty t.t_ty Pretty.print_ty t1
    | _ ->
	assert false

let rec itype_v gl env = function
  | DTpure ty ->
      ITpure (Denv.ty_of_dty ty)
  | DTarrow (bl, c) ->
      let env, bl = map_fold_left (ibinder gl) env bl in
      ITarrow (bl, itype_c gl env c)

and itype_c gl env c =
  let tyv = itype_v gl env c.dc_result_type in
  { ic_result_type = tyv;
    ic_effect      = ieffect env c.dc_effect;
    ic_pre         = pre env c.dc_pre;
    ic_post        = post env c.dc_post; }

and ibinder gl env (x, ty, tyv) =
  let tyv = itype_v gl env tyv in
  let ty = Denv.ty_of_dty ty in
  let env, v = iadd_local env x ty in
  env, (v, tyv)

let mk_iexpr loc ty d = { iexpr_desc = d; iexpr_loc = loc; iexpr_type = ty }

let mk_t_if gl f =
  let ty = ty_app (find_ts gl "bool") [] in
  t_if f (t_app (find_ls gl "True") [] ty) (t_app (find_ls gl "False") [] ty)

(* apply ls to a list of expressions, introducing let's if necessary

  ls [e1; e2; ...; en]
->
  let x1 = e1 in
  let x2 = e2 in
  ...
  let xn = en in
  ls(x1,x2,...,xn)
*)
let make_logic_app gl loc ty ls el =
  let rec make args = function
    | [] ->
        begin match ls.ls_value with
          | Some _ -> IElogic (t_app ls (List.rev args) ty)
          | None -> IElogic (mk_t_if gl (f_app ls (List.rev args)))
        end
    | ({ iexpr_desc = IElogic t }, _) :: r ->
	make (t :: args) r
    | ({ iexpr_desc = IElocal v }, _) :: r ->
	make (t_var v.i_pgm :: args) r
    | ({ iexpr_desc = IEglobal s; iexpr_type = ty }, _) :: r ->
	make (t_app s.p_ls [] ty :: args) r
    | (e, _) :: r ->
	let v = create_ivsymbol (id_user "x" loc) e.iexpr_type in
	let d = mk_iexpr loc ty (make (t_var v.i_pgm :: args) r) in
	IElet (v, e, d)
  in
  make [] el

let is_ts_ref gl ts =
  try ts_equal ts (find_ts gl "ref") with Not_found -> false

let is_reference_type gl ty  = match ty.ty_node with
  | Ty.Tyapp (ts, _) -> is_ts_ref gl ts
  | _ -> false

(* same thing, but for an abritrary expression f (not an application)
   f [e1; e2; ...; en]
-> let x1 = e1 in ... let xn = en in (...((f x1) x2)... xn)
*)
let make_app _gl loc ty f el =
  let rec make k = function
    | [] ->
	k f
(***
    | ({ iexpr_type = ty } as e, tye) :: r when is_reference_type gl ty ->
	begin match e.iexpr_desc with
	  | IElocal v ->
	      make (fun f -> mk_iexpr loc tye (IEapply_ref (k f, R.Rlocal v))) r
	  | IEglobal v ->
	      make (fun f -> mk_iexpr loc tye (IEapply_ref (k f, R.Rglobal v))) r
	  | _ ->
	      let v = create_pvsymbol (id_user "x" loc) (tpure e.iexpr_type) in
	      let d =
		make (fun f -> mk_iexpr loc tye (IEapply_ref (k f, R.Rlocal v))) r
	      in
	      mk_iexpr loc ty (IElet (v, e, d))
	end
***)
    | ({ iexpr_desc = IElocal v }, tye) :: r ->
	make (fun f -> mk_iexpr loc tye (IEapply (k f, v))) r
    | (e, tye) :: r ->
	let v = create_ivsymbol (id_user "x" loc) e.iexpr_type in
	let d = make (fun f -> mk_iexpr loc tye (IEapply (k f, v))) r in
	mk_iexpr loc ty (IElet (v, e, d))
  in
  make (fun f -> f) el

let rec ipattern env p = 
  let env, n = ipattern_node env p.pat_node in
  env, { ipat_pat = p; ipat_node = n }

and ipattern_node env p = 
  let add1 env vs = 
    (* TODO: incorrect when vs is not pure ? *)
    let i = 
      { i_pgm = create_vsymbol (id_clone vs.vs_name) vs.vs_ty; i_logic = vs } 
    in
    Mstr.add vs.vs_name.id_string i env, i
  in
  match p with
  | Term.Pwild -> 
      env, IPwild
  | Term.Papp (ls, pl) -> 
      let env, pl = map_fold_left ipattern env pl in
      env, IPapp (ls, pl)
  | Term.Por (p1, p2) -> 
      let env, p1 = ipattern env p1 in
      let _  , p2 = ipattern env p2 in
      env, IPor (p1, p2)
  | Term.Pvar vs ->
      let env, v = add1 env vs in
      env, IPvar v
  | Term.Pas (p, vs) ->
      let env, v = add1 env vs in
      let env, p = ipattern env p in
      env, IPas (p, v)

(* [iexpr] translates dexpr into iexpr
   [env : vsymbol Mstr.t] maps strings to vsymbols for local variables *)

let rec iexpr gl env e =
  let ty = Denv.ty_of_dty e.dexpr_type in
  let d = iexpr_desc gl env e.dexpr_loc ty e.dexpr_desc in
  { iexpr_desc = d; iexpr_type = ty; iexpr_loc = e.dexpr_loc }

and iexpr_desc gl env loc ty = function
  | DEconstant c ->
      IElogic (t_const c)
  | DElocal (x, _tyv) ->
      IElocal (Mstr.find x env)
  | DEglobal (s, _tyv) ->
      IEglobal s
  | DElogic ls ->
      begin match ls.ls_args, ls.ls_value with
	| [], Some _ ->
	    IElogic (t_app ls [] ty)
	| [], None ->
            IElogic (mk_t_if gl (f_app ls []))
	| al, _ ->
	    errorm ~loc "function symbol %s is expecting %d arguments"
	      ls.ls_name.id_string (List.length al)
      end
  | DEapply (e1, e2) ->
      let f, args = decompose_app gl env e1 [iexpr gl env e2, ty] in
      begin match f.dexpr_desc with
	| DElogic ls ->
	    let n = List.length ls.ls_args in
	    if List.length args <> n then
	      errorm ~loc "function symbol %s is expecting %d arguments"
		ls.ls_name.id_string n;
	    make_logic_app gl loc ty ls args
	| _ ->
	    let f = iexpr gl env f in
	    (make_app gl loc ty f args).iexpr_desc
      end
  | DEfun (bl, e1) ->
      let env, bl = map_fold_left (ibinder gl) env bl in
      IEfun (bl, itriple gl env e1)
  | DElet (x, e1, e2) ->
      let e1 = iexpr gl env e1 in
      let v = create_ivsymbol (id_user x.id x.id_loc) e1.iexpr_type in
      let env = Mstr.add x.id v env in
      IElet (v, e1, iexpr gl env e2)
  | DEletrec (dl, e1) ->
      let env, dl = iletrec gl env dl in
      let e1 = iexpr gl env e1 in
      IEletrec (dl, e1)

  | DEsequence (e1, e2) ->
      let vs = create_ivsymbol (id_fresh "_") (ty_app (ts_tuple 0) []) in
      IElet (vs, iexpr gl env e1, iexpr gl env e2)
  | DEif (e1, e2, e3) ->
      IEif (iexpr gl env e1, iexpr gl env e2, iexpr gl env e3)
  | DEloop (la, e1) ->
      let la =
	{ loop_invariant =
	    option_map (Denv.fmla (lenv env)) la.dloop_invariant;
	  loop_variant   =
	    option_map (variant loc (lenv env)) la.dloop_variant; }
      in
      IEloop (la, iexpr gl env e1)
  | DElazy (op, e1, e2) ->
      IElazy (op, iexpr gl env e1, iexpr gl env e2)
  | DEmatch (e1, bl) ->
      let e1 = iexpr gl env e1 in
      let branch (p, e) =
        let _, p = Denv.pattern (lenv env) p in 
	let env, p = ipattern env p in
	(p, iexpr gl env e)
      in
      let bl = List.map branch bl in
      let v = create_ivsymbol (id_user "x" loc) e1.iexpr_type in
      IElet (v, e1, mk_iexpr loc ty (IEmatch (v, bl)))
  | DEabsurd ->
      IEabsurd
  | DEraise (ls, e) ->
      IEraise (ls, option_map (iexpr gl env) e)
  | DEtry (e, hl) ->
      let handler (ls, x, h) =
	let x, env = match x with
	  | Some x ->
	      let ty = match ls.ls_args with [ty] -> ty | _ -> assert false in
	      let v = create_ivsymbol (id_fresh x) ty in
	      Some v, Mstr.add x v env
	  | None ->
	      None, env
	in
	(ls, x, iexpr gl env h)
      in
      IEtry (iexpr gl env e, List.map handler hl)
  | DEfor (x, e1, d, e2, inv, e3) ->
      let e1 = iexpr gl env e1 in
      let e2 = iexpr gl env e2 in
      let vx = create_ivsymbol (id_user x.id x.id_loc) e1.iexpr_type in
      let env = Mstr.add x.id vx env in
      let inv = option_map (Denv.fmla (lenv env)) inv in
      let e3 = iexpr gl env e3 in
      let v1 = create_ivsymbol (id_user "for_start" loc) e1.iexpr_type in
      let v2 = create_ivsymbol (id_user "for_end" loc)   e2.iexpr_type in
      IElet (v1, e1, mk_iexpr loc ty (
      IElet (v2, e2, mk_iexpr loc ty (
      IEfor (vx, v1, d, v2, inv, e3)))))

  | DEassert (k, f) ->
      let f = Denv.fmla (lenv env) f in
      IEassert (k, f)
  | DElabel (s, e1) ->
      let ty = Ty.ty_app (find_ts gl "label") [] in
      let v = create_ivsymbol (id_fresh s) ty in
      let env = Mstr.add s v env in
      IElabel (v.i_pgm, iexpr gl env e1)
  | DEany c ->
      let c = itype_c gl env c in
      IEany c

and decompose_app gl env e args = match e.dexpr_desc with
  | DEapply (e1, e2) ->
      let ty = Denv.ty_of_dty e.dexpr_type in
      decompose_app gl env e1 ((iexpr gl env e2, ty) :: args)
  | _ ->
      e, args

and iletrec gl env dl =
  (* add all functions into env, and compute local env *)
  let step1 env ((x, dty), bl, var, t) =
    let ty = Denv.ty_of_dty dty in
    let v = create_ivsymbol (id_user x.id x.id_loc) ty in
    let env = Mstr.add x.id v env in
    env, (v, bl, var, t)
  in
  let env, dl = map_fold_left step1 env dl in
  (* then translate variants and bodies *)
  let step2 (v, bl, var, (_,e,_ as t)) =
    let loc = e.dexpr_loc in (* FIXME *)
    let env, bl = map_fold_left (ibinder gl) env bl in
    let var = option_map (variant loc (lenv env)) var in
    let t = itriple gl env t in
    let var, t = match var with
      | None ->
	  None, t
      | Some (phi, r) ->
	  let p, e, q = t in
	  let phi0 = create_ivsymbol (id_fresh "variant") phi.t_ty in
	  let e_phi = { iexpr_desc = IElogic phi; iexpr_type = phi.t_ty;
			iexpr_loc = e.iexpr_loc } in
	  let e = { e with iexpr_desc = IElet (phi0, e_phi, e) } in
	  Some (phi0, phi, r), (p, e, q)
    in
    (v, bl, var, t)
  in
  let dl = List.map step2 dl in
  (* finally, check variants are all absent or all present and consistent *)
  let error e =
    errorm ~loc:e.iexpr_loc "variants must be all present or all absent"
  in
  begin match dl with
    | [] ->
	assert false
    | (_, _, None, _) :: r ->
	let check_no_variant (_,_,var,(_,e,_)) = if var <> None then error e in
	List.iter check_no_variant r
    | (_, _, Some (_, _, ps), _) :: r ->
	let check_variant (_,_,var,(_,e,_)) = match var with
	  | None -> error e
	  | Some (_, _, ps') -> if not (ls_equal ps ps') then
	      errorm ~loc:e.iexpr_loc
		"variants must share the same order relation"
	in
	List.iter check_variant r
  end;
  env, dl

and itriple gl env (p, e, q) =
  let p = Denv.fmla (lenv env) p in
  let e = iexpr gl env e in
  let q = post env q in
  (p, e, q)

(* pretty-printing (for debugging) *)

open Pp
open Pretty

let rec print_iexpr fmt e = match e.iexpr_desc with
  | IElogic t ->
      print_term fmt t
  | IElocal v ->
      fprintf fmt "<local %a>" print_vs v.i_pgm
  | IEglobal s ->
      fprintf fmt "<global %a>" print_ls s.p_ls
  | IEapply (e, v) ->
      fprintf fmt "@[((%a) %a)@]" print_iexpr e print_vs v.i_pgm
  (* | IEapply_ref (e, r) -> *)
  (*     fprintf fmt "@[((%a) <ref %a>)@]" print_iexpr e print_reference r *)
  | IEfun (_, (_,e,_)) ->
      fprintf fmt "@[fun _ ->@ %a@]" print_iexpr e
  | IElet (v, e1, e2) ->
      fprintf fmt "@[let %a = %a in@ %a@]" print_vs v.i_pgm
	print_iexpr e1 print_iexpr e2

  | _ ->
      fprintf fmt "<other>"

(* phase 3: effect inference **********)

let rec term_effect uc ef t = match t.t_node with
  (* | Term.Tapp (ls, [t]) when ls_equal ls (find_ls uc "prefix !") -> *)
  (*     let r = reference_of_term t in *)
  (*     E.add_read r ef *)
  | _ ->
      t_fold (term_effect uc) (fmla_effect uc) ef t

and fmla_effect uc ef f =
  f_fold (term_effect uc) (fmla_effect uc) ef f

let post_effect env ef ((v,q),ql) =
  let exn_effect ef (_,(_,q)) = fmla_effect env ef q in
  let ef = List.fold_left exn_effect (fmla_effect env ef q) ql in
  let not_result = function
    | R.Rlocal vs -> not (vs_equal vs.pv_vs v)
    | R.Rglobal _ -> true
  in
  E.filter not_result ef

let reference env = function
  | IRlocal  i -> R.Rlocal (Mvs.find i.i_pgm env)
  | IRglobal s -> R.Rglobal s 

let effect env e =
  let reads ef r = E.add_read (reference env r) ef in
  let writes ef r = E.add_write (reference env r) ef in
  let raises ef l = E.add_raise l ef in
  let ef = List.fold_left reads E.empty e.ie_reads in
  let ef = List.fold_left writes ef e.ie_writes in
  List.fold_left raises ef e.ie_raises

let add_local env i v =
  let vs = create_pvsymbol (id_clone i.i_pgm.vs_name) ~vs:i.i_logic v in
  Mvs.add i.i_pgm vs env, vs

let rec type_v env = function
  | ITpure ty ->
      tpure ty
  | ITarrow (bl, c) ->
      let env, bl = add_binders env bl in
      tarrow bl (type_c env c)

and type_c env c = {
  c_result_type = type_v env c.ic_result_type;
  c_effect      = effect env c.ic_effect;
  c_pre         = c.ic_pre;
  c_post        = c.ic_post; 
}

and add_binders env bl =
  map_fold_left add_binder env bl

and add_binder env (i, v) =
  let v = type_v env v in
  let env, vs = add_local env i v in
  env, vs

let rec pattern env p = 
  let env, n = pattern_node env p.ipat_node in
  env, { ppat_pat = p.ipat_pat; ppat_node = n }

and pattern_node env p = 
  let add1 env i = 
    let v = 
      create_pvsymbol (id_clone i.i_pgm.vs_name) ~vs:i.i_logic 
	(tpure i.i_pgm.vs_ty) 
    in
    Mvs.add i.i_pgm v env, v
  in
  match p with
  | IPwild -> 
      env, Pwild
  | IPapp (ls, pl) -> 
      let env, pl = map_fold_left pattern env pl in
      env, Papp (ls, pl)
  | IPor (p1, p2) -> 
      let env, p1 = pattern env p1 in
      let _  , p2 = pattern env p2 in
      env, Por (p1, p2)
  | IPvar vs ->
      let env, v = add1 env vs in
      env, Pvar v
  | IPas (p, vs) ->
      let env, v = add1 env vs in
      let env, p = pattern env p in
      env, Pas (p, v)

let make_apply loc e1 ty c =
  let x = create_pvsymbol (id_fresh "f") (tpure e1.expr_type) in
  let v = c.c_result_type and ef = c.c_effect in
  let any_c = { expr_desc = Eany c; expr_type = ty;
		expr_type_v = v; expr_effect = ef; expr_loc = loc } in
  Elet (x, e1, any_c), v, ef

let exn_check = ref true
let without_exn_check f x =
  if !exn_check then begin
    exn_check := false;
    try let y = f x in exn_check := true; y
    with e -> exn_check := true; raise e
  end else
    f x

(*s Pure expressions. Used in [Slazy_and] and [Slazy_or] to decide
    whether to use [strict_bool_and_] and [strict_bool_or_] or not. *)

let rec is_pure_expr e =
  E.no_side_effect e.expr_effect &&
  match e.expr_desc with
  | Elocal _ | Elogic _ -> true
  | Eif (e1, e2, e3) -> is_pure_expr e1 && is_pure_expr e2 && is_pure_expr e3
  | Elet (_, e1, e2) -> is_pure_expr e1 && is_pure_expr e2
  | Elabel (_, e1) -> is_pure_expr e1
  | Eany c -> E.no_side_effect c.c_effect
  | Eassert _ | Etry _ | Efor _ | Eraise _ | Ematch _
  | Eloop _ | Eletrec _ | Efun _
  | Eglobal _ | Eabsurd -> false (* TODO: improve *)

let mk_expr loc ty ef d =
  { expr_desc = d; expr_type = ty; expr_type_v = tpure ty;
    expr_effect = ef; expr_loc = loc }

let mk_simple_expr loc ty d = mk_expr loc ty E.empty d

let mk_bool_constant loc gl ls =
  let ty = ty_app (find_ts gl "bool") [] in
  { expr_desc = Elogic (t_app ls [] ty); expr_type = ty; expr_type_v = tpure ty;
    expr_effect = E.empty; expr_loc = loc }

let mk_false loc gl = mk_bool_constant loc gl (find_ls gl "False")
let mk_true  loc gl = mk_bool_constant loc gl (find_ls gl "True")

(* types do not contain inner reference types *)

let rec check_type ?(noref=false) gl loc ty = match ty.ty_node with
  | Ty.Tyapp (ts, tyl) when ts_equal ts ts_arrow ->
      List.iter (check_type gl loc) tyl
  | Ty.Tyapp (ts, _) when noref && is_ts_ref gl ts ->
      errorm ~loc "inner reference types are not allowed"
  | Ty.Tyapp (_, tyl) ->
      List.iter (check_type ~noref:true gl loc) tyl
  | Ty.Tyvar _ ->
      ()

(* Saturation of postconditions: a postcondition must be set for
   any possibly raised exception *)

(* let warning_no_post loc x =  *)
(*   wprintf loc "no postcondition for exception %a; false inserted@\n"  *)
(*     Ident.print x; *)
(*   if werror then exit 1 *)

let saturation loc ef (a,al) =
  let xs = ef.E.raises in
  let check (x,_) =
    if not (Sexn.mem x xs) then
      errorm ~loc "exception %a cannot be raised" print_ls x
  in
  List.iter check al;
  let set_post x =
    try
      x, List.assoc x al
    with Not_found ->
      (* warning_no_post loc x; *)
      x, (exn_v_result x, f_false)
  in
  (a, List.map set_post (Sexn.elements xs))

let type_v_unit _env = tpure (ty_app (ts_tuple 0) [])

(* [expr] translates iexpr into expr
   [env : type_v Mvs.t] maps local variables to their types *)

let rec expr gl env e =
  let ty = e.iexpr_type in
  let loc = e.iexpr_loc in
  let d, v, ef = expr_desc gl env loc ty e.iexpr_desc in
  check_type gl loc ty; (* TODO: improve efficiency *)
  { expr_desc = d; expr_type = ty;
    expr_type_v = v; expr_effect = ef; expr_loc = loc }

and expr_desc gl env loc ty = function
  | IElogic t ->
      let ef = term_effect gl E.empty t in
      Elogic t, tpure ty, ef
  | IElocal vs ->
      let vs = Mvs.find vs.i_pgm env in
      Elocal vs, vs.pv_tv, E.empty
  | IEglobal s ->
      Eglobal s, s.p_tv, E.empty
  | IEapply (e1, vs) ->
      let e1 = expr gl env e1 in
      (* printf "e1 : %a@." print_type_v e1.expr_type_v; *)
      let vs = Mvs.find vs.i_pgm env in
      let c = apply_type_v_var e1.expr_type_v vs in
      make_apply loc e1 ty c
  (* | IEapply_ref (e1, r) -> *)
  (*     let e1 = expr gl env e1 in *)
  (*     if occur_type_v r e1.expr_type_v then *)
  (* 	errorm ~loc "this application would create an alias"; *)
  (*     let c = apply_type_v_ref e1.expr_type_v r in *)
  (*     make_apply loc e1 ty c *)
  | IEfun (bl, t) ->
      let env, bl = add_binders env bl in
      let t, c = triple gl env t in
      Efun (bl, t), tarrow bl c, E.empty
  | IElet (v, e1, e2) ->
      let e1 = expr gl env e1 in
      let env, v = add_local env v e1.expr_type_v in
      let e2 = expr gl env e2 in
      let ef = E.union e1.expr_effect e2.expr_effect in
      let r = R.Rlocal v in
      if occur_type_v r e2.expr_type_v then
	errorm ~loc "local reference would escape its scope";
      let ef = E.remove_reference r ef in
      Elet (v, e1, e2), e2.expr_type_v, ef
  | IEletrec (dl, e1) ->
      let env, dl = letrec gl env dl in
      let e1 = expr gl env e1 in
      Eletrec (dl, e1), e1.expr_type_v, e1.expr_effect

  | IEif (e1, e2, e3) ->
      let e1 = expr gl env e1 in
      let e2 = expr gl env e2 in
      let e3 = expr gl env e3 in
      let ef = E.union e1.expr_effect e2.expr_effect in
      let ef = E.union ef             e3.expr_effect in
      if not (eq_type_v e2.expr_type_v e3.expr_type_v) then
	errorm ~loc "cannot branch on functions";
      Eif (e1, e2, e3), e2.expr_type_v, ef
  | IEloop (a, e1) ->
      let e1 = expr gl env e1 in
      let ef = e1.expr_effect in
      let ef = match a.loop_invariant with
	| Some f -> fmla_effect gl ef f
	| None -> ef
      in
      let ef = match a.loop_variant with
	| Some (t, _) -> term_effect gl ef t
	| None        -> ef
      in
      Eloop (a, e1), type_v_unit gl, ef
  | IElazy (op, e1, e2) ->
      let e1 = expr gl env e1 in
      let e2 = expr gl env e2 in
      let ef = E.union e1.expr_effect e2.expr_effect in
      let d =
	if is_pure_expr e2 then
	  let ls = match op with
	    | Pgm_ptree.LazyAnd -> find_ls gl "andb"
	    | Pgm_ptree.LazyOr  -> find_ls gl "orb"
	  in
	  let v1 = create_pvsymbol (id_fresh "lazy") (tpure ty) in
	  let v2 = create_pvsymbol (id_fresh "lazy") (tpure ty) in
	  let t = t_app ls [t_var v1.pv_vs; t_var v2.pv_vs] ty in
	  Elet (v1, e1,
		mk_expr loc ty ef
		  (Elet (v2, e2, mk_simple_expr loc ty (Elogic t))))
	else match op with
	  | Pgm_ptree.LazyAnd ->
	      Eif (e1, e2, mk_false loc gl)
	  | Pgm_ptree.LazyOr ->
	      Eif (e1, mk_true loc gl, e2)
      in
      d, tpure ty, ef
  | IEmatch (i, bl) ->
      let v = Mvs.find i.i_pgm env in
      (* if is_reference_type gl v.vs_ty then *)
      (* 	errorm ~loc "cannot match over a reference"; *)
      let branch ef (p, e) =
	let env, p = pattern env p in
	let e = expr gl env e in
	let ef = E.union ef e.expr_effect in
	ef, (p, e)
      in
      let ef, bl = map_fold_left branch E.empty bl in
      Ematch (v, bl), tpure ty, ef
  | IEabsurd ->
      Eabsurd, tpure ty, E.empty
  | IEraise (x, e1) ->
      let e1 = option_map (expr gl env) e1 in
      let ef = match e1 with Some e1 -> e1.expr_effect | None -> E.empty in
      let ef = E.add_raise x ef in
      Eraise (x, e1), tpure ty, ef
  | IEtry (e1, hl) ->
      let e1 = expr gl env e1 in
      let ef = e1.expr_effect in
      let handler (x, v, h) =
	if not (Sexn.mem x ef.E.raises) && !exn_check then
	  errorm ~loc "exception %a cannot be raised" print_ls x;
	let env, v = match x.ls_args, v with
	  | [ty], Some v -> 
	      let env, v = add_local env v (tpure ty) in env, Some v
	  | [], None -> 
	      env, None
	  | _ -> assert false
	in
	x, v, expr gl env h
      in
      let ef = List.fold_left (fun e (x,_,_) -> E.remove_raise x e) ef hl in
      let hl = List.map handler hl in
      let ef =
	List.fold_left (fun e (_,_,h) -> E.union e h.expr_effect) ef hl
      in
      Etry (e1, hl), tpure ty, ef
  | IEfor (x, v1, d, v2, inv, e3) ->
      let v1 = Mvs.find v1.i_pgm env in
      let v2 = Mvs.find v2.i_pgm env in
      let env, x = add_local env x (tpure v1.pv_vs.vs_ty) in
      let e3 = expr gl env e3 in
      let ef = match inv with
	| Some f -> fmla_effect gl e3.expr_effect f
	| None -> e3.expr_effect
      in
      Efor (x, v1, d, v2, inv, e3), type_v_unit gl, ef

  | IEassert (k, f) ->
      let ef = fmla_effect gl E.empty f in
      Eassert (k, f), tpure ty, ef
  | IElabel (lab, e1) ->
      let e1 = expr gl env e1 in
      Elabel (lab, e1), e1.expr_type_v, e1.expr_effect
  | IEany c ->
      let c = type_c env c in
      Eany c, c.c_result_type, c.c_effect

and triple gl env (p, e, q) =
  let e = expr gl env e in
  let q = saturation e.expr_loc e.expr_effect q in
  let ef = post_effect gl (fmla_effect gl e.expr_effect p) q in
  let e = { e with expr_effect = ef } in
  let c =
    { c_result_type = e.expr_type_v;
      c_effect      = ef;
      c_pre         = p;
      c_post        = q }
  in
  (p, e, q), c

and letrec gl env dl = (* : env * recfun list *)
  let binders (i, bl, var, t) =
    let env, bl = add_binders env bl in
    let variant (i, t, ls) = 
      (create_pvsymbol (id_clone i.i_pgm.vs_name) ~vs:i.i_logic 
	 (tpure i.i_pgm.vs_ty), t, ls)
    in
    (i, bl, env, option_map variant var, t)
  in
  let dl = List.map binders dl in
  (* effects are computed as a least fixpoint
     [m] maps each function to its current effect *)
  let make_env env ?decvar m =
    let add1 env (i, bl, _, var, _) =
      let c = Mvs.find i.i_pgm m in
      let c = match decvar, var with
	| Some phi0, Some (_, phi, r) ->
	    let decphi = f_app r [phi; t_var phi0] in
	    { c with c_pre = f_and decphi c.c_pre }
	| _ ->
	    c
      in
      let env, _ = add_local env i (tarrow bl c) in
      env
    in
    List.fold_left add1 env dl
  in
  let one_step m0 =
    let type1 m (i, bl, env, var, t) =
      let decvar = option_map (fun (v,_,_) -> v.pv_vs) var in
      let env = make_env env ?decvar m0 in
      let t, c = triple gl env t in
      let v = create_pvsymbol (id_clone i.i_pgm.vs_name) ~vs:i.i_logic
	(tarrow bl c) in
      Mvs.add i.i_pgm c m, (v, bl, var, t)
    in
    map_fold_left type1 Mvs.empty dl
  in
  let rec fixpoint m =
    let m', dl' = one_step m in
    let same_effect (i,_,_,_,_) =
      E.equal (Mvs.find i.i_pgm m).c_effect (Mvs.find i.i_pgm m').c_effect
    in
    if List.for_all same_effect dl then m, dl' else fixpoint m'
  in
  let add_empty_effect m (i, bl, _, _, (p, _, q)) =
    let tyl, ty = uncurrying i.i_pgm.vs_ty in
    assert (List.length bl = List.length tyl);
    let c = { c_result_type = tpure ty;
	      c_pre = p; c_effect = E.empty; c_post = q; }
    in
    Mvs.add i.i_pgm c m
  in
  let m0 = List.fold_left add_empty_effect Mvs.empty dl in
  let m, dl = fixpoint m0 in
  make_env env m, dl

(* freshness analysis

   checks that values of type 'a ref are only freshly allocated
   term:bool indicates if we are in terminal position in the expression
   (to allow functions to return fresh references) *)

let rec fresh_expr gl ~term locals e = match e.expr_desc with
  (* | Elocal vs when is_reference_type gl vs.vs_ty *)
  (*   && (not term || not (Svs.mem vs locals)) -> *)
  (*     errorm ~loc:e.expr_loc "not a fresh reference (could create an alias)" *)
  | Elogic _ | Elocal _ | Eglobal _ ->
      ()
  | Efun (_, t) ->
      fresh_triple gl t
  | Elet (vs, e1, e2) ->
      fresh_expr gl ~term:false locals                      e1;
      fresh_expr gl ~term       (Sid.add vs.pv_name locals) e2
  | Eletrec (fl, e1) ->
      List.iter (fun (_, _, _, t) -> fresh_triple gl t) fl;
      fresh_expr gl ~term locals e1

  | Eif (e1, e2, e3) ->
      fresh_expr gl ~term:false locals e1;
      fresh_expr gl ~term       locals e2;
      fresh_expr gl ~term       locals e3
  | Eloop (_, e1) ->
      fresh_expr gl ~term:false locals e1
  | Ematch (_, bl) ->
      let branch (_, e1) = fresh_expr gl ~term locals e1 in
      List.iter branch bl
  | Eabsurd | Eraise (_, None) ->
      ()
  | Eraise (_, Some e1) ->
      fresh_expr gl ~term:false locals e1
  | Etry (e1, hl) ->
      fresh_expr gl ~term:false locals e1;
      List.iter (fun (_, _, e2) -> fresh_expr gl ~term locals e2) hl
  | Efor (_, _, _, _, _, e1) ->
      fresh_expr gl ~term:false locals e1

  | Elabel (_, e) ->
      fresh_expr gl ~term locals e
  | Eassert _ | Eany _ ->
      ()

and fresh_triple gl (_, e, _) =
  fresh_expr gl ~term:true Sid.empty e

(* pretty-printing (for debugging) *)

let rec print_expr fmt e = match e.expr_desc with
  | Elogic t ->
      print_term fmt t
  | Elocal vs ->
      fprintf fmt "<local %a>" print_vs vs.pv_vs
  | Eglobal ls ->
      fprintf fmt "<global %a>" print_ls ls.p_ls
  | Efun (_, t) ->
      fprintf fmt "@[fun _ ->@ %a@]" print_triple t
  | Elet (v, e1, e2) ->
      fprintf fmt "@[let %a = %a in@ %a@]" print_vs v.pv_vs
	print_expr e1 print_expr e2

  | Eif (e1, e2, e3) ->
      fprintf fmt "@[if %a@ then@ %a else@ %a@]"
	print_expr e1 print_expr e2 print_expr e3

  | Eany c ->
      fprintf fmt "@[[any %a]@]" print_type_c c

  | _ ->
      fprintf fmt "<other>"

and print_triple fmt (p, e, q) =
  fprintf fmt "@[{%a}@ %a@ {%a}@]" print_pre p print_expr e print_post q

and print_pre fmt _ =
  fprintf fmt "<pre>"

and print_post fmt _ =
  fprintf fmt "<post>"

and print_recfun fmt (v, _bl, _, t) =
  fprintf fmt "@[rec %a _ = %a@]" print_vs v print_triple t

(* typing declarations (combines the three phases together) *)

let type_expr gl e =
  let denv = create_denv gl in
  let e = dexpr denv e in
  let e = iexpr gl Mstr.empty e in
  let e = expr gl Mvs.empty e in
  fresh_expr gl ~term:true Sid.empty e;
  e

let type_type uc ty =
  let denv = create_denv uc in
  let dty = Typing.dty denv.denv ty in
  Denv.ty_of_dty dty

let add_logic_decl uc ls =
  try
    add_logic_decl (Decl.create_logic_decl [ls, None]) uc
  with Theory.ClashSymbol _ ->
    let loc = loc_of_ls ls in
    errorm ?loc "clash with previous symbol %s" ls.ls_name.id_string

let add_global loc x tyv uc =
  try
    let ps = create_psymbol (id_user x loc) tyv in
    ps, add_psymbol ps uc
  with Pgm_module.ClashSymbol _ ->
    errorm ~loc "clash with previous symbol %s" x

let add_global_if_pure gl { p_ls = ls } = match ls.ls_args, ls.ls_value with
  | [], Some { ty_node = Ty.Tyapp (ts, _) } when ts_equal ts ts_arrow -> gl
  | [], Some _ -> add_logic_decl gl ls
  | _ -> gl

let add_exception loc x ty uc =
  try
    let tyl = match ty with None -> [] | Some ty -> [ty] in
    let id = id_user x loc in
    let ls = create_lsymbol id tyl (Some (ty_app (find_ts uc "exn") [])) in
    add_esymbol ls uc
  with ClashSymbol _ ->
    errorm ~loc "clash with previous exception %s" x

let rec polymorphic_pure_type ty = match ty.ty_node with
  | Ty.Tyvar _ -> true
  | Ty.Tyapp (_, tyl) -> List.exists polymorphic_pure_type tyl

let cannot_be_generalized gl = function
  | Tpure { ty_node = Ty.Tyapp (ts, [ty]) } when is_ts_ref gl ts ->
      polymorphic_pure_type ty
  | Tpure { ty_node = Ty.Tyvar _ } ->
      true
  | Tpure _ | Tarrow _ ->
      false

let check_type_vars ~loc vars ty =
  let h = Htv.create 17 in
  List.iter (fun v -> Htv.add h v ()) vars;
  let rec check ty = match ty.ty_node with
    | Ty.Tyvar v when not (Htv.mem h v) -> 
	errorm ~loc "unbound type variable '%s" v.tv_name.id_string
    | Ty.Tyvar _ ->
	()
    | Ty.Tyapp (_, tyl) ->
	List.iter check tyl
  in
  check ty

let find_module penv lmod q id = match q with
  | [] ->
      (* local module *)
      Mnm.find id lmod
  | _ :: _ ->
      (* theory in file f *)
      Pgm_env.find_module penv q id

(* env = to retrieve theories from the loadpath
   penv = to retrieve modules from the loadpath
   lmod = local modules *)
let rec decl ~wp env penv lmod uc = function
  | Pgm_ptree.Dlogic dl ->
      Pgm_module.parse_logic_decls env dl uc
  | Pgm_ptree.Dlet (id, e) ->
      let e = type_expr uc e in
      Debug.dprintf debug "@[--typing %s-----@\n  %a@\n%a@]@."
	id.id print_expr e print_type_v e.expr_type_v;
      let ls, uc = add_global id.id_loc id.id e.expr_type_v uc in
      let d = Dlet (ls, e) in
      let uc = add_decl d uc in
      if wp then Pgm_wp.decl uc d else uc
  | Pgm_ptree.Dletrec dl ->
      let denv = create_denv uc in
      let _, dl = dletrec denv dl in
      let _, dl = iletrec uc Mstr.empty dl in
      let _, dl = letrec uc Mvs.empty dl in
      let one uc (v, _, _, _ as d) =
	let tyv = v.pv_tv in
	let loc = loc_of_id v.pv_name in
	let id = v.pv_name.id_string in
	(* if Debug.test_flag debug then *)
        (*   eprintf "@[--typing %s-----@\n  %a@.%a@]@." *)
	(*     id print_recfun d print_type_v tyv; *)
	let ps, uc = add_global loc id tyv uc in
	uc, (ps, d)
      in
      let uc, dl = map_fold_left one uc dl in
      let d = Dletrec dl in
      let uc = add_decl d uc in
      if wp then Pgm_wp.decl uc d else uc
  | Pgm_ptree.Dparam (id, tyv) ->
      let loc = id.id_loc in
      let denv = create_denv uc in
      let tyv = dtype_v denv tyv in
      let tyv = itype_v uc Mstr.empty tyv in
      let tyv = type_v Mvs.empty tyv in
      if cannot_be_generalized uc tyv then errorm ~loc "cannot be generalized";
      let ps, uc = add_global loc id.id tyv uc in
      let uc = add_global_if_pure uc ps in
      add_decl (Dparam (ps, tyv)) uc (* TODO: is it really needed? *)
  | Pgm_ptree.Dexn (id, ty) ->
      let ty = option_map (type_type uc) ty in
      add_exception id.id_loc id.id ty uc
  (* modules *) 
  | Pgm_ptree.Duse (qid, imp_exp, use_as) ->
      let loc = Typing.qloc qid in
      let q, id = Typing.split_qualid qid in
      let m =
	try
	  find_module penv lmod q id
	with Not_found | Pgm_env.ModuleNotFound _ -> 
	  errorm ~loc "@[unbound module %a@]" print_qualid qid
      in
      let n = match use_as with
	| None -> Some (m.m_name.id_string)
	| Some x -> Some x.id
      in
      begin try match imp_exp with
	| Nothing ->
	    (* use T = namespace T use_export T end *)
	    let uc = open_namespace uc in
	    let uc = use_export uc m in
	    close_namespace uc false n
	| Import ->
	    (* use import T = namespace T use_export T end import T *)
	    let uc = open_namespace uc in
	    let uc = use_export uc m in
	    close_namespace uc true n
	| Export ->
	    use_export uc m
      with ClashSymbol s -> 
	errorm ~loc "clash with previous symbol %s" s
      end
  | Pgm_ptree.Dnamespace (id, import, dl) ->
      let loc = id.id_loc in
      let uc = open_namespace uc in
      let uc = List.fold_left (decl ~wp env penv lmod) uc dl in
      begin try close_namespace uc import (Some id.id)
      with ClashSymbol s -> errorm ~loc "clash with previous symbol %s" s end
  | Pgm_ptree.Dmutable_type (id, args, model) ->
      let loc = id.id_loc in
      let id = id_user id.id loc in
      let denv = Typing.create_denv (theory_uc uc) in
      let args = 
	List.map 
	  (fun x -> tvsymbol_of_type_var (Typing.find_user_type_var x.id denv))
	  args
      in
      let model = 
	option_map 
	  (fun ty -> let dty = Typing.dty denv ty in Denv.ty_of_dty dty)
	  model 
      in
      option_iter (check_type_vars ~loc args) model;
      let mt = create_mtsymbol id args model in
      let uc = 
	let d = Decl.create_ty_decl [mt.mt_abstr, Decl.Tabstract] in
	Pgm_module.add_logic_decl d uc 
      in
      add_mtsymbol mt uc

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. testl"
End:
*)

(*
TODO:

- mutually recursive functions: allow order relation to be specified only once

- exhaustivity of pattern-matching (in WP?)

- do not add global references into the theory (add_global_if_pure)

- polymorphic let?

- ghost
*)
