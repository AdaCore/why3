(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2012                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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

open Why3
open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Env
open Ptree
open Mlw_dtree
open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl
open Mlw_pretty
open Mlw_module
open Mlw_wp
open Mlw_dty

(** errors *)

exception DuplicateProgVar of string
exception DuplicateTypeVar of string
(*
exception PredicateExpected
exception TermExpected
exception FSymExpected of lsymbol
exception PSymExpected of lsymbol
exception ClashTheory of string
exception UnboundTheory of qualid
exception UnboundType of string list
*)
exception UnboundTypeVar of string
exception UnboundSymbol of string list

let error = Loc.error
let errorm = Loc.errorm

let qloc = Typing.qloc
let print_qualid = Typing.print_qualid

let () = Exn_printer.register (fun fmt e -> match e with
  | DuplicateTypeVar s ->
      Format.fprintf fmt "Type parameter %s is used twice" s
  | DuplicateProgVar s ->
      Format.fprintf fmt "Parameter %s is used twice" s
(*
  | PredicateExpected ->
      Format.fprintf fmt "syntax error: predicate expected"
  | TermExpected ->
      Format.fprintf fmt "syntax error: term expected"
  | FSymExpected ls ->
      Format.fprintf fmt "%a is not a function symbol" Pretty.print_ls ls
  | PSymExpected ls ->
      Format.fprintf fmt "%a is not a predicate symbol" Pretty.print_ls ls
  | ClashTheory s ->
      Format.fprintf fmt "Clash with previous theory %s" s
  | UnboundTheory q ->
      Format.fprintf fmt "unbound theory %a" print_qualid q
  | UnboundType sl ->
      Format.fprintf fmt "Unbound type '%a'"
        (Pp.print_list Pp.dot Pp.pp_print_string) sl
*)
  | UnboundTypeVar s ->
      Format.fprintf fmt "unbound type variable '%s" s
  | UnboundSymbol sl ->
      Format.fprintf fmt "Unbound symbol '%a'"
        (Pp.print_list Pp.dot Format.pp_print_string) sl
  | _ -> raise e)

(* TODO: let type_only = Debug.test_flag Typing.debug_type_only in *)

type denv = {
  uc     : module_uc;
  locals : (tvars * dity) Mstr.t;
  tvars  : tvars;
  uloc   : Ptree.loc option;
}

let create_denv uc = {
  uc     = uc;
  locals = Mstr.empty;
  tvars  = empty_tvars;
  uloc   = None;
}

(** Typing type expressions *)

let rec dity_of_pty ~user denv = function
  | Ptree.PPTtyvar id ->
      create_user_type_variable id
  | Ptree.PPTtyapp (pl, p) ->
      let dl = List.map (dity_of_pty ~user denv) pl in
      let x = Typing.string_list_of_qualid [] p in
      begin
        try
          let its = ns_find_it (get_namespace denv.uc) x in
          its_app ~user its dl
        with Not_found -> try
          let ts = ns_find_ts (Theory.get_namespace (get_theory denv.uc)) x in
          ts_app ts dl
        with Not_found ->
          errorm ~loc:(qloc p) "unbound symbol %a" print_qualid p
      end
  | Ptree.PPTtuple pl ->
      ts_app (ts_tuple (List.length pl)) (List.map (dity_of_pty ~user denv) pl)

(** Typing program expressions *)

let dity_int  = ts_app ts_int  []
let dity_real = ts_app ts_real []
let dity_bool = ts_app ts_bool []
let dity_unit = ts_app ts_unit []
let dity_mark = ts_app ts_mark []

let expected_type ?(weak=false) e dity =
  unify ~weak e.de_type dity

let rec extract_labels labs loc e = match e.Ptree.expr_desc with
  | Ptree.Enamed (Ptree.Lstr s, e) -> extract_labels (s :: labs) loc e
  | Ptree.Enamed (Ptree.Lpos p, e) -> extract_labels labs (Some p) e
  | Ptree.Ecast  (e, ty) ->
      let labs, loc, d = extract_labels labs loc e in
      labs, loc, Ptree.Ecast ({ e with Ptree.expr_desc = d }, ty)
  | e -> List.rev labs, loc, e

let rec decompose_app args e = match e.Ptree.expr_desc with
  | Eapply (e1, e2) -> decompose_app (e2 :: args) e1
  | _ -> e, args

(* record parsing *)

let parse_record uc fll =
  let pl = match fll with
    | [] -> raise EmptyRecord
    | (pl,_)::_ -> pl in
  let its = match pl.pl_args with
    | [{ vtv_ity = { ity_node = Ityapp (its,_,_) }}] -> its
    | _ -> raise (BadRecordField pl.pl_ls) in
  let cs, pjl = match find_constructors (get_known uc) its with
    | [cs,pjl] -> cs, List.map (exn_option (BadRecordField pl.pl_ls)) pjl
    | _ -> raise (BadRecordField pl.pl_ls) in
  let pjs = List.fold_left (fun s pj -> Sls.add pj.pl_ls s) Sls.empty pjl in
  let flm = List.fold_left (fun m (pj,v) -> let pj = pj.pl_ls in
    if not (Sls.mem pj pjs) then raise (BadRecordField pj) else
      Mls.add_new (DuplicateRecordField (cs.pl_ls,pj)) pj v m)
    Mls.empty fll
  in
  cs,pjl,flm

let find_field uc (p,e) =
  let x = Typing.string_list_of_qualid [] p in
  try match ns_find_ps (get_namespace uc) x with
    | PL pl -> (pl,e)
    | _ -> errorm ~loc:(qloc p) "bad record field %a" print_qualid p
  with Not_found -> errorm ~loc:(qloc p) "unbound symbol %a" print_qualid p

let find_pure_field uc (p,e) =
  let x = Typing.string_list_of_qualid [] p in
  try ns_find_ls (Theory.get_namespace (get_theory uc)) x, e
  with Not_found -> errorm ~loc:(qloc p) "unbound symbol %a" print_qualid p

let pure_record uc = function
  | [] -> raise Decl.EmptyRecord
  | (p,_)::_ ->
      let x = Typing.string_list_of_qualid [] p in
      begin try ignore (ns_find_ps (get_namespace uc) x); false
      with Not_found -> true end

let hidden_pl ~loc pl =
  { de_desc = DEglobal_pl pl;
    de_type = specialize_plsymbol pl;
    de_loc  = loc; de_lab = [] }

let hidden_ls ~loc ls =
  { de_desc = DEglobal_ls ls;
    de_type = specialize_lsymbol ls;
    de_loc  = loc; de_lab = [] }

(* helper functions for let-expansion *)
let test_var e = match e.de_desc with
  | DElocal _ | DEglobal_pv _ -> true
  | _ -> false

let mk_var e =
  if test_var e then e else
  { de_desc = DElocal "q";
    de_type = e.de_type;
    de_loc  = e.de_loc;
    de_lab  = [] }

let mk_id s loc =
  { id = s; id_loc = loc; id_lab = [] }

let mk_dexpr desc dity loc labs =
  { de_desc = desc; de_type = dity; de_loc = loc; de_lab = labs }

let mk_let ~loc ~uloc e (desc,dity) =
  if test_var e then desc, dity else
  let loc = def_option loc uloc in
  let e1 = mk_dexpr desc dity loc [] in
  DElet (mk_id "q" loc, e, e1), dity

(* patterns *)

let add_var id dity denv =
  let tvars = add_tvars denv.tvars dity in
  let locals = Mstr.add id.id (tvars,dity) denv.locals in
  { denv with locals = locals; tvars = tvars }

let specialize_qualid uc p =
  let x = Typing.string_list_of_qualid [] p in
  try match ns_find_ps (get_namespace uc) x with
    | PV pv -> DEglobal_pv pv, specialize_pvsymbol pv
    | PS ps -> DEglobal_ps ps, specialize_psymbol  ps
    | PL pl -> DEglobal_pl pl, specialize_plsymbol pl
    | PX xs ->
        errorm ~loc:(qloc p) "unexpected exception symbol %a" print_xs xs
  with Not_found -> try
    let ls = ns_find_ls (Theory.get_namespace (get_theory uc)) x in
    DEglobal_ls ls, specialize_lsymbol ls
  with Not_found ->
    errorm ~loc:(qloc p) "unbound symbol %a" print_qualid p

let find_xsymbol uc p =
  let x = Typing.string_list_of_qualid [] p in
  try match ns_find_ps (get_namespace uc) x with
    | PX xs -> xs
    | _ -> errorm ~loc:(qloc p) "exception symbol expected"
  with Not_found ->
    errorm ~loc:(qloc p) "unbound symbol %a" print_qualid p

let find_variant_ls uc p =
  let x = Typing.string_list_of_qualid [] p in
  try match ns_find_ps (get_namespace uc) x with
    | _ -> errorm ~loc:(qloc p) "%a is not a binary relation" print_qualid p
  with Not_found -> try
    match ns_find_ls (Theory.get_namespace (get_theory uc)) x with
      | { ls_args = [u;v]; ls_value = None } as ls when ty_equal u v -> ls
      | ls ->
          errorm ~loc:(qloc p) "%a is not a binary relation" Pretty.print_ls ls
  with Not_found ->
    errorm ~loc:(qloc p) "unbound symbol %a" print_qualid p

let rec dpattern denv ({ pat_loc = loc } as pp) = match pp.pat_desc with
  | Ptree.PPpwild ->
      PPwild, create_type_variable (), denv
  | Ptree.PPpvar id ->
      let dity = create_type_variable () in
      PPvar (Denv.create_user_id id), dity, add_var id dity denv
  | Ptree.PPpapp (q,ppl) ->
      let sym, dity = specialize_qualid denv.uc q in
      dpat_app denv (mk_dexpr sym dity loc []) ppl
  | Ptree.PPprec fl when pure_record denv.uc fl ->
      let kn = Theory.get_known (get_theory denv.uc) in
      let fl = List.map (find_pure_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc Decl.parse_record kn fl in
      let wild = { pat_desc = Ptree.PPpwild; pat_loc = loc } in
      let get_val pj = Mls.find_def wild pj flm in
      dpat_app denv (hidden_ls ~loc cs) (List.map get_val pjl)
  | Ptree.PPprec fl ->
      let fl = List.map (find_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc parse_record denv.uc fl in
      let wild = { pat_desc = Ptree.PPpwild; pat_loc = loc } in
      let get_val pj = Mls.find_def wild pj.pl_ls flm in
      dpat_app denv (hidden_pl ~loc cs) (List.map get_val pjl)
  | Ptree.PPptuple ppl ->
      let cs = fs_tuple (List.length ppl) in
      dpat_app denv (hidden_ls ~loc cs) ppl
  | Ptree.PPpor (pp1, pp2) ->
      let pp1, dity1, denv = dpattern denv pp1 in
      let pp2, dity2, denv = dpattern denv pp2 in
      Loc.try2 loc unify dity1 dity2;
      PPor (pp1, pp2), dity1, denv
  | Ptree.PPpas (pp, id) ->
      let pp, dity, denv = dpattern denv pp in
      PPas (pp, Denv.create_user_id id), dity, add_var id dity denv

and dpat_app denv ({ de_loc = loc } as de) ppl =
  let add_pp pp (ppl, tyl, denv) =
    let pp,ty,denv = dpattern denv pp in pp::ppl,ty::tyl,denv in
  let ppl, tyl, denv = List.fold_right add_pp ppl ([],[],denv) in
  let pp = match de.de_desc with
    | DEglobal_pl pl -> Mlw_expr.PPpapp (pl, ppl)
    | DEglobal_ls ls -> PPlapp (ls, ppl)
    | DEglobal_pv pv -> errorm ~loc "%a is not a constructor" print_pv pv
    | DEglobal_ps ps -> errorm ~loc "%a is not a constructor" print_ps ps
    | _ -> assert false
  in
  let res = create_type_variable () in
  Loc.try2 loc unify de.de_type (make_arrow_type tyl res);
  pp, res, denv

(* specifications *)

let dbinders denv bl =
  let dbinder (id,pty) (denv,bl,tyl) =
    let dity = match pty with
      | Some pty -> dity_of_pty ~user:true denv pty
      | None -> create_type_variable () in
    add_var id dity denv, (id,false,dity)::bl, dity::tyl
  in
  List.fold_right dbinder bl (denv,[],[])

let deff_of_peff uc pe =
  { deff_reads  = List.map (fun le -> false, le) pe.pe_reads;
    deff_writes = List.map (fun le -> false, le) pe.pe_writes;
    deff_raises = List.map (fun q -> false, find_xsymbol uc q) pe.pe_raises; }

let dxpost uc ql = List.map (fun (q,f) -> find_xsymbol uc q, f) ql

let rec dtype_c denv tyc =
  let tyv, dity = dtype_v denv tyc.pc_result_type in
  { dc_result = tyv;
    dc_effect = deff_of_peff denv.uc tyc.pc_effect;
    dc_pre    = tyc.pc_pre;
    dc_post   = fst tyc.pc_post;
    dc_xpost  = dxpost denv.uc (snd tyc.pc_post); },
  dity

and dtype_v denv = function
  | Tpure pty ->
      let dity = dity_of_pty ~user:true denv pty in
      DSpecV (false,dity), dity
  | Tarrow (bl,tyc) ->
      let denv,bl,tyl = dbinders denv bl in
      let tyc,dity = dtype_c denv tyc in
      DSpecA (bl,tyc), make_arrow_type tyl dity

let dvariant uc = function
  | Some (le, Some q) -> [le, Some (find_variant_ls uc q)]
  | Some (le, None) -> [le, None]
  | None -> []
(* TODO: accept a list of variants in the surface language
  List.map (fun (le,q) -> le, Util.option_map (find_variant_ls uc) q) var
*)

(* expressions *)

let de_unit ~loc = hidden_ls ~loc (fs_tuple 0)

let de_app e el =
  let res = create_type_variable () in
  let tyl = List.map (fun a -> a.de_type) el in
  expected_type e (make_arrow_type tyl res);
  DEapply (e, el), res

let rec dexpr denv e =
  let loc = e.Ptree.expr_loc in
  let labs, uloc, d = extract_labels [] denv.uloc e in
  let denv = { denv with uloc = uloc } in
  let d, ty = de_desc denv loc d in
  let loc = def_option loc uloc in
  mk_dexpr d ty loc labs

and de_desc denv loc = function
  | Ptree.Eident (Qident {id=x}) when Mstr.mem x denv.locals ->
      (* local variable *)
      let tvs, dity = Mstr.find x denv.locals in
      let dity = specialize_scheme tvs dity in
      DElocal x, dity
  | Ptree.Eident p ->
      specialize_qualid denv.uc p
  | Ptree.Eapply (e1, e2) ->
      let e, el = decompose_app [e2] e1 in
      let el = List.map (dexpr denv) el in
      de_app (dexpr denv e) el
  | Ptree.Elet (id, e1, e2) ->
      let e1 = dexpr denv e1 in
      let dity = e1.de_type in
      let tvars = match e1.de_desc with
        | DEfun _ -> denv.tvars
        | _ -> add_tvars denv.tvars dity in
      let locals = Mstr.add id.id (tvars, dity) denv.locals in
      let denv = { denv with locals = locals; tvars = tvars } in
      let e2 = dexpr denv e2 in
      DElet (id, e1, e2), e2.de_type
  | Ptree.Eletrec (rdl, e1) ->
      let rdl = dletrec denv rdl in
      let add_one denv ({ id = id }, dity, _) =
        { denv with locals = Mstr.add id (denv.tvars, dity) denv.locals } in
      let denv = List.fold_left add_one denv rdl in
      let e1 = dexpr denv e1 in
      DEletrec (rdl, e1), e1.de_type
  | Ptree.Efun (bl, tr) ->
      let lam, dity = dlambda denv bl None tr in
      DEfun lam, dity
  | Ptree.Ecast (e1, pty) ->
      let e1 = dexpr denv e1 in
      expected_type e1 (dity_of_pty ~user:false denv pty);
      e1.de_desc, e1.de_type
  | Ptree.Enamed _ ->
      assert false
  | Ptree.Esequence (e1, e2) ->
      let e1 = dexpr denv e1 in
      expected_type e1 dity_unit;
      let e2 = dexpr denv e2 in
      DElet (mk_id "_" loc, e1, e2), e2.de_type
  | Ptree.Eif (e1, e2, e3) ->
      let e1 = dexpr denv e1 in
      expected_type e1 dity_bool;
      let e2 = dexpr denv e2 in
      let e3 = dexpr denv e3 in
      expected_type e3 e2.de_type;
      DEif (e1, e2, e3), e2.de_type
  | Ptree.Etuple el ->
      let ls = fs_tuple (List.length el) in
      let el = List.map (dexpr denv) el in
      de_app (hidden_ls ~loc ls) el
  | Ptree.Erecord fl when pure_record denv.uc fl ->
      let kn = Theory.get_known (get_theory denv.uc) in
      let fl = List.map (find_pure_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc Decl.parse_record kn fl in
      let get_val pj = match Mls.find_opt pj flm with
        | Some e -> dexpr denv e
        | None -> error ~loc (Decl.RecordFieldMissing (cs,pj)) in
      de_app (hidden_ls ~loc cs) (List.map get_val pjl)
  | Ptree.Erecord fl ->
      let fl = List.map (find_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc parse_record denv.uc fl in
      let get_val pj = match Mls.find_opt pj.pl_ls flm with
        | Some e -> dexpr denv e
        | None -> error ~loc (Decl.RecordFieldMissing (cs.pl_ls,pj.pl_ls)) in
      de_app (hidden_pl ~loc cs) (List.map get_val pjl)
  | Ptree.Eupdate (e1, fl) when pure_record denv.uc fl ->
      let e1 = dexpr denv e1 in
      let e0 = mk_var e1 in
      let kn = Theory.get_known (get_theory denv.uc) in
      let fl = List.map (find_pure_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc Decl.parse_record kn fl in
      let get_val pj = match Mls.find_opt pj flm with
        | Some e -> dexpr denv e
        | None ->
            let d, dity = de_app (hidden_ls ~loc pj) [e0] in
            mk_dexpr d dity loc [] in
      let res = de_app (hidden_ls ~loc cs) (List.map get_val pjl) in
      mk_let ~loc ~uloc:denv.uloc e1 res
  | Ptree.Eupdate (e1, fl) ->
      let e1 = dexpr denv e1 in
      let e0 = mk_var e1 in
      let fl = List.map (find_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc parse_record denv.uc fl in
      let get_val pj = match Mls.find_opt pj.pl_ls flm with
        | Some e -> dexpr denv e
        | None ->
            let d, dity = de_app (hidden_pl ~loc pj) [e0] in
            mk_dexpr d dity loc [] in
      let res = de_app (hidden_pl ~loc cs) (List.map get_val pjl) in
      mk_let ~loc ~uloc:denv.uloc e1 res
  | Ptree.Eassign (e1, q, e2) ->
      let fl = { expr_desc = Eident q; expr_loc = loc } in
      let e1 = { expr_desc = Eapply (fl,e1); expr_loc = loc } in
      let e1 = dexpr denv e1 in
      let e2 = dexpr denv e2 in
      expected_type ~weak:true e2 e1.de_type;
      DEassign (e1, e2), dity_unit
  | Ptree.Econstant (ConstInt _ as c) ->
      DEconstant c, dity_int
  | Ptree.Econstant (ConstReal _ as c) ->
      DEconstant c, dity_real
  | Ptree.Enot e1 ->
      let e1 = dexpr denv e1 in
      expected_type e1 dity_bool;
      DEnot e1, dity_bool
  | Ptree.Elazy (op, e1, e2) ->
      let e1 = dexpr denv e1 in
      let e2 = dexpr denv e2 in
      expected_type e1 dity_bool;
      expected_type e2 dity_bool;
      DElazy (op, e1, e2), dity_bool
  | Ptree.Ematch (e1, bl) ->
      let e1 = dexpr denv e1 in
      let res = create_type_variable () in
      let branch (pp,e) =
        let ppat, dity, denv = dpattern denv pp in
        let e = dexpr denv e in
        Loc.try2 pp.pat_loc unify dity e1.de_type;
        expected_type e res;
        ppat, e in
      DEmatch (e1, List.map branch bl), res
  | Ptree.Eraise (q, e1) ->
      let res = create_type_variable () in
      let xs = find_xsymbol denv.uc q in
      let dity = specialize_xsymbol xs in
      let e1 = match e1 with
        | Some e1 -> dexpr denv e1
        | None when ity_equal xs.xs_ity ity_unit -> de_unit ~loc
        | _ -> errorm ~loc "exception argument expected" in
      expected_type e1 dity;
      DEraise (xs, e1), res
  | Ptree.Etry (e1, cl) ->
      let e1 = dexpr denv e1 in
      let branch (q, id, e) =
        let xs = find_xsymbol denv.uc q in
        let dity = specialize_xsymbol xs in
        let id, denv = match id with
          | Some id -> id, add_var id dity denv
          | None -> mk_id "void" loc, denv in
        xs, id, dexpr denv e
      in
      let cl = List.map branch cl in
      DEtry (e1, cl), e1.de_type
  | Ptree.Eabsurd ->
      DEabsurd, create_type_variable ()
  | Ptree.Eassert (ak, lexpr) ->
      DEassert (ak, lexpr), dity_unit
  | Ptree.Emark (id, e1) ->
      let e1 = dexpr denv e1 in
      DEmark (id, e1), e1.de_type
  | Ptree.Eany tyc ->
      let tyc, dity = dtype_c denv tyc in
      DEany tyc, dity
  | Ptree.Eloop ({ loop_invariant = inv; loop_variant = var }, e1) ->
      let e1 = dexpr denv e1 in
      let var = dvariant denv.uc var in
      expected_type e1 dity_unit;
      DEloop (var,inv,e1), e1.de_type
  | Ptree.Efor (id, efrom, dir, eto, inv, e1) ->
      let efrom = dexpr denv efrom in
      let eto = dexpr denv eto in
      let denv = add_var id dity_int denv in
      let e1 = dexpr denv e1 in
      expected_type efrom dity_int;
      expected_type eto dity_int;
      expected_type e1 dity_unit;
      DEfor (id,efrom,dir,eto,inv,e1), e1.de_type
  | Ptree.Eabstract (_e1, _post) ->
      assert false (*TODO*)

and dletrec denv rdl =
  (* add all functions into environment *)
  let add_one denv (id, bl, var, tr) =
    let res = create_type_variable () in
    add_var id res denv, (id, res, bl, var, tr) in
  let denv, rdl = Util.map_fold_left add_one denv rdl in
  (* then type-check all of them and unify *)
  let type_one (id, res, bl, var, tr) =
    let lam, dity = dlambda denv bl var tr in
    Loc.try2 id.id_loc unify dity res;
    id, dity, lam in
  List.map type_one rdl

and dlambda denv bl var (p, e, (q, xq)) =
  let denv,bl,tyl = dbinders denv bl in
  let e = dexpr denv e in
  let var = dvariant denv.uc var in
  let xq = dxpost denv.uc xq in
  (bl, var, p, e, q, xq), make_arrow_type tyl e.de_type

(** stage 2 *)

type lenv = {
  mod_uc   : module_uc;
  let_vars : let_var Mstr.t;
  log_vars : vsymbol Mstr.t;
  log_denv : Typing.denv;
}

let create_lenv uc = {
  mod_uc   = use_export_theory uc Mlw_wp.th_mark;
  let_vars = Mstr.empty;
  log_vars = Mstr.empty;
  log_denv = Typing.denv_empty;
}

let rec dty_of_ty ty = match ty.ty_node with
  | Ty.Tyvar v ->
      Typing.create_user_type_var v.tv_name.id_string
  | Ty.Tyapp (ts, tyl) ->
      Denv.tyapp ts (List.map dty_of_ty tyl)

let create_post lenv x ty f =
  let res = create_vsymbol (id_fresh x) ty in
  let log_vars = Mstr.add x res lenv.log_vars in
  let log_denv = Typing.add_var x (dty_of_ty ty) lenv.log_denv in
  let f = Typing.type_fmla (get_theory lenv.mod_uc) log_denv log_vars f in
  create_post res f

let create_pre lenv f =
  Typing.type_fmla (get_theory lenv.mod_uc) lenv.log_denv lenv.log_vars f

let create_variant lenv (t,r) =
  let t =
    Typing.type_term (get_theory lenv.mod_uc) lenv.log_denv lenv.log_vars t in
  { v_term = t; v_rel = r }

let add_local x lv lenv = match lv with
  | LetA _ ->
      { lenv with let_vars = Mstr.add x lv lenv.let_vars }
  | LetV pv ->
      let dty = dty_of_ty pv.pv_vs.vs_ty in
      { mod_uc   = lenv.mod_uc;
        let_vars = Mstr.add x lv lenv.let_vars;
        log_vars = Mstr.add x pv.pv_vs lenv.log_vars;
        log_denv = Typing.add_var x dty lenv.log_denv }

exception DuplicateException of xsymbol

let binders lenv bl =
  let binder lenv (id, ghost, dity) =
    let vtv = vty_value ~ghost (ity_of_dity dity) in
    let pv = create_pvsymbol (Denv.create_user_id id) vtv in
    add_local id.id (LetV pv) lenv, pv in
  Util.map_fold_left binder lenv bl

let xpost lenv xq =
  let add_exn m (xs,f) =
    let f = create_post lenv "result" (ty_of_ity xs.xs_ity) f in
    Mexn.add_new (DuplicateException xs) xs f m in
  List.fold_left add_exn Mexn.empty xq

let eff_of_deff _lenv _deff = eff_empty (* TODO *)

let rec type_c lenv dtyc =
  let result = type_v lenv dtyc.dc_result in
  let ty = match result with
    | SpecV v -> ty_of_ity v.vtv_ity
    | SpecA _ -> ty_unit in
  { c_pre    = create_pre lenv dtyc.dc_pre;
    c_effect = eff_of_deff lenv dtyc.dc_effect;
    c_result = result;
    c_post   = create_post lenv "result" ty dtyc.dc_post;
    c_xpost  = xpost lenv dtyc.dc_xpost; }

and type_v lenv = function
  | DSpecV (ghost,v) ->
      SpecV (vty_value ~ghost (ity_of_dity v))
  | DSpecA (bl,tyc) ->
      let lenv, pvl = binders lenv bl in
      SpecA (pvl, type_c lenv tyc)

(* expressions *)

let rec expr lenv de = match de.de_desc with
  | DElocal x ->
      assert (Mstr.mem x lenv.let_vars);
      begin match Mstr.find x lenv.let_vars with
      | LetV pv -> e_value pv
      | LetA ps -> e_cast ps (vty_of_dity de.de_type)
      end
  | DElet (x, { de_desc = DEfun lam }, de2) ->
      let def = expr_fun lenv x lam in
      let lenv = add_local x.id (LetA def.rec_ps) lenv in
      let e2 = expr lenv de2 in
      e_rec [def] e2
  | DEfun lam ->
      let x = mk_id "fn" de.de_loc in
      let def = expr_fun lenv x lam in
      let e2 = e_cast def.rec_ps (VTarrow def.rec_ps.ps_vta) in
      e_rec [def] e2
  | DElet (x, de1, de2) ->
      let e1 = expr lenv de1 in
      let def1 = create_let_defn (Denv.create_user_id x) e1 in
      let lenv = add_local x.id def1.let_var lenv in
      let e2 = expr lenv de2 in
      e_let def1 e2
  | DEletrec (rdl, de1) ->
      let rdl = expr_rec lenv rdl in
      let add_rd { rec_ps = ps } = add_local ps.ps_name.id_string (LetA ps) in
      let e1 = expr (List.fold_right add_rd rdl lenv) de1 in
      e_rec rdl e1
  | DEapply (de1, del) ->
      let el = List.map (expr lenv) del in
      begin match de1.de_desc with
        | DEglobal_pl pls -> e_plapp pls el (ity_of_dity de.de_type)
        | DEglobal_ls ls  -> e_lapp  ls  el (ity_of_dity de.de_type)
        | _               -> e_app (expr lenv de1) el
      end
  | DEglobal_pv pv ->
      e_value pv
  | DEglobal_ps ps ->
      e_cast ps (vty_of_dity de.de_type)
  | DEglobal_pl pl ->
      assert (pl.pl_ls.ls_args = []);
      e_plapp pl [] (ity_of_dity de.de_type)
  | DEglobal_ls ls ->
      assert (ls.ls_args = []);
      e_lapp ls [] (ity_of_dity de.de_type)
  | DEif (de1, de2, de3) ->
      e_if (expr lenv de1) (expr lenv de2) (expr lenv de3)
  | DEassign (de1, de2) ->
      e_assign (expr lenv de1) (expr lenv de2)
  | DEconstant c ->
      e_const c
  | DElazy (LazyAnd, de1, de2) ->
      e_lazy_and (expr lenv de1) (expr lenv de2)
  | DElazy (LazyOr, de1, de2) ->
      e_lazy_or (expr lenv de1) (expr lenv de2)
  | DEnot de1 ->
      e_not (expr lenv de1)
  | DEmatch (de1, bl) ->
      let e1 = expr lenv de1 in
      let vtv = vtv_of_expr e1 in
      let branch (pp,de) =
        let vm, pp = make_ppattern pp vtv in
        let lenv = Mstr.fold (fun s pv -> add_local s (LetV pv)) vm lenv in
        pp, expr lenv de in
      e_case e1 (List.map branch bl)
  | DEassert (ak, f) ->
      let ak = match ak with
        | Ptree.Aassert -> Aassert
        | Ptree.Aassume -> Aassume
        | Ptree.Acheck  -> Acheck in
      e_assert ak (create_pre lenv f)
  | DEabsurd ->
      e_absurd (ity_of_dity de.de_type)
  | DEraise (xs, de1) ->
      e_raise xs (expr lenv de1) (ity_of_dity de.de_type)
  | DEtry (de1, bl) ->
      let e1 = expr lenv de1 in
      let branch (xs,id,de) =
        let vtv = vty_value xs.xs_ity in
        let pv = create_pvsymbol (Denv.create_user_id id) vtv in
        let lenv = add_local id.id (LetV pv) lenv in
        xs, pv, expr lenv de in
      e_try e1 (List.map branch bl)
  | DEmark (x, de1) ->
      let ld = create_let_defn (Denv.create_user_id x) e_setmark in
      let lenv = add_local x.id ld.let_var lenv in
      e_let ld (expr lenv de1)
  | DEany dtyc ->
      e_any (type_c lenv dtyc)
  | DEghost de1 ->
      e_ghost (expr lenv de1)
  | DEloop (var,inv,de1) ->
      let inv = match inv with
        | Some inv -> create_pre lenv inv
        | None -> t_true in
      let var = List.map (create_variant lenv) var in
      e_loop inv var (expr lenv de1)
  | DEfor (x,defrom,dir,deto,inv,de1) ->
      let efrom = expr lenv defrom in
      let eto = expr lenv deto in
      let pv = create_pvsymbol (Denv.create_user_id x) (vty_value ity_int) in
      let lenv = add_local x.id (LetV pv) lenv in
      let dir = match dir with
        | Ptree.To -> To
        | Ptree.Downto -> DownTo in
      let inv = match inv with
        | Some inv -> create_pre lenv inv
        | None -> t_true in
      let e1 = expr lenv de1 in
      e_for pv efrom dir eto inv e1

and expr_rec lenv rdl =
  let step1 lenv (id, dity, lam) =
    let vta = match vty_of_dity dity with
      | VTarrow vta -> vta
      | VTvalue _ -> assert false in
    let ps = create_psymbol (Denv.create_user_id id) vta vars_empty in
    add_local id.id (LetA ps) lenv, (ps, lam) in
  let lenv, rdl = Util.map_fold_left step1 lenv rdl in
  let step2 (ps, lam) = ps, expr_lam lenv lam in
  create_rec_defn (List.map step2 rdl)

and expr_fun lenv x lam =
  let lam = expr_lam lenv lam in
  create_fun_defn (Denv.create_user_id x) lam

and expr_lam lenv (bl, var, p, e, q, xq) =
  let lenv, pvl = binders lenv bl in
  let e = expr lenv e in
  let ty = match e.e_vty with
    | VTarrow _ -> ty_unit
    | VTvalue vtv -> ty_of_ity vtv.vtv_ity
  in
  { l_args = pvl;
    l_variant = List.map (create_variant lenv) var;
    l_pre = create_pre lenv p;
    l_expr = e;
    l_post = create_post lenv "result" ty q;
    l_xpost = xpost lenv xq; }

(** Type declaration *)

type tys = ProgTS of itysymbol | PureTS of tysymbol

let find_tysymbol q uc =
  let loc = Typing.qloc q in
  let sl = Typing.string_list_of_qualid [] q in
  try ProgTS (ns_find_it (get_namespace uc) sl)
  with Not_found ->
  try PureTS (ns_find_ts (Theory.get_namespace (get_theory uc)) sl)
  with Not_found -> error ~loc (UnboundSymbol sl)

let look_for_loc tdl s =
  let look_id loc id = if id.id = s then Some id.id_loc else loc in
  let look_pj loc (id,_) = option_fold look_id loc id in
  let look_cs loc (csloc,id,pjl) =
    let loc = if id.id = s then Some csloc else loc in
    List.fold_left look_pj loc pjl in
  let look_fl loc f = look_id loc f.f_ident in
  let look loc d =
    let loc = look_id loc d.td_ident in
    match d.td_def with
      | TDabstract | TDalias _ -> loc
      | TDalgebraic csl -> List.fold_left look_cs loc csl
      | TDrecord fl -> List.fold_left look_fl loc fl
  in
  List.fold_left look None tdl

let add_types uc tdl =
  let add m d =
    let id = d.td_ident.id in
    Mstr.add_new (Loc.Located (d.td_loc, ClashSymbol id)) id d m in
  let def = List.fold_left add Mstr.empty tdl in

  (* detect cycles *)

  let rec cyc_visit x d seen = match Mstr.find_opt x seen with
    | Some true -> seen
    | Some false -> errorm ~loc:d.td_loc "Cyclic type definition"
    | None ->
        let ts_seen seen = function
          | Qident { id = x } ->
              begin try cyc_visit x (Mstr.find x def) seen
              with Not_found -> seen end
          | _ -> seen in
        let rec check seen = function
          | PPTtyvar _ -> seen
          | PPTtyapp (tyl,q) -> List.fold_left check (ts_seen seen q) tyl
          | PPTtuple tyl -> List.fold_left check seen tyl in
        let seen = match d.td_def with
          | TDabstract | TDalgebraic _ | TDrecord _ -> seen
          | TDalias ty -> check (Mstr.add x false seen) ty in
        Mstr.add x true seen in
  ignore (Mstr.fold cyc_visit def Mstr.empty);

  (* detect mutable types *)

  let mutables = Hashtbl.create 5 in
  let rec mut_visit x =
    try Hashtbl.find mutables x
    with Not_found ->
      let ts_mut = function
        | Qident { id = x } when Mstr.mem x def -> mut_visit x
        | q ->
            begin match find_tysymbol q uc with
              | ProgTS s -> s.its_regs <> []
              | PureTS _ -> false end in
      let rec check = function
        | PPTtyvar _ -> false
        | PPTtyapp (tyl,q) -> ts_mut q || List.exists check tyl
        | PPTtuple tyl -> List.exists check tyl in
      Hashtbl.replace mutables x false;
      let mut = match (Mstr.find x def).td_def with
        | TDabstract -> false
        | TDalias ty -> check ty
        | TDalgebraic csl ->
            let proj (_,pty) = check pty in
            List.exists (fun (_,_,l) -> List.exists proj l) csl
        | TDrecord fl ->
            let field f = f.f_mutable || check f.f_pty in
            List.exists field fl in
      Hashtbl.replace mutables x mut;
      mut
  in
  Mstr.iter (fun x _ -> ignore (mut_visit x)) def;

  (* create type symbols and predefinitions for mutable types *)

  let tysymbols = Hashtbl.create 5 in
  let predefs = Hashtbl.create 5 in
  let rec its_visit x =
    try match Hashtbl.find tysymbols x with
      | Some ts -> ts
      | None ->
          let loc = (Mstr.find x def).td_loc in
          errorm ~loc "Mutable type in a recursive type definition"
    with Not_found ->
      let d = Mstr.find x def in
      let add_tv acc id =
        let e = Loc.Located (id.id_loc, DuplicateTypeVar id.id) in
        let tv = create_tvsymbol (Denv.create_user_id id) in
        Mstr.add_new e id.id tv acc in
      let vars = List.fold_left add_tv Mstr.empty d.td_params in
      let vl = List.map (fun id -> Mstr.find id.id vars) d.td_params in
      let id = Denv.create_user_id d.td_ident in
      let abst = d.td_vis = Abstract in
      let priv = d.td_vis = Private in
      Hashtbl.add tysymbols x None;
      let get_ts = function
        | Qident { id = x } when Mstr.mem x def -> ProgTS (its_visit x)
        | q -> find_tysymbol q uc
      in
      let rec parse = function
        | PPTtyvar { id = v ; id_loc = loc } ->
            let e = Loc.Located (loc, UnboundTypeVar v) in
            ity_var (Mstr.find_exn e v vars)
        | PPTtyapp (tyl,q) ->
            let tyl = List.map parse tyl in
            begin match get_ts q with
              | PureTS ts -> Loc.try2 (Typing.qloc q) ity_pur ts tyl
              | ProgTS ts -> Loc.try2 (Typing.qloc q) ity_app_fresh ts tyl
            end
        | PPTtuple tyl ->
            let ts = ts_tuple (List.length tyl) in
            ity_pur ts (List.map parse tyl)
      in
      let ts = match d.td_def with
        | TDalias ty ->
            let def = parse ty in
            let rl = Sreg.elements def.ity_vars.vars_reg in
            create_itysymbol id ~abst ~priv vl rl (Some def)
        | TDalgebraic csl when Hashtbl.find mutables x ->
            let projs = Hashtbl.create 5 in
            (* to check projections' types we must fix the tyvars *)
            let add s v = let t = ity_var v in ity_match s t t in
            let sbs = List.fold_left add ity_subst_empty vl in
            let mk_proj s (id,pty) =
              let ity = parse pty in
              let vtv = vty_value ity in
              match id with
                | None ->
                    let pv = create_pvsymbol (id_fresh "pj") vtv in
                    Sreg.union s ity.ity_vars.vars_reg, (pv, false)
                | Some id ->
                    try
                      let pv = Hashtbl.find projs id.id in
                      let ty = pv.pv_vtv.vtv_ity in
                      (* once we have ghost/mutable fields in algebraics,
                         don't forget to check here that they coincide, too *)
                      ignore (Loc.try3 id.id_loc ity_match sbs ty ity);
                      s, (pv, true)
                    with Not_found ->
                      let pv = create_pvsymbol (Denv.create_user_id id) vtv in
                      Hashtbl.replace projs id.id pv;
                      Sreg.union s ity.ity_vars.vars_reg, (pv, true)
            in
            let mk_constr s (_loc,cid,pjl) =
              let s,pjl = Util.map_fold_left mk_proj s pjl in
              s, (Denv.create_user_id cid, pjl)
            in
            let s,def = Util.map_fold_left mk_constr Sreg.empty csl in
            Hashtbl.replace predefs x def;
            create_itysymbol id ~abst ~priv vl (Sreg.elements s) None
        | TDrecord fl when Hashtbl.find mutables x ->
            let mk_field s f =
              let ghost = f.f_ghost in
              let ity = parse f.f_pty in
              let fid = Denv.create_user_id f.f_ident in
              let s,mut = if f.f_mutable then
                let r = create_region fid ity in
                Sreg.add r s, Some r
              else
                Sreg.union s ity.ity_vars.vars_reg, None
              in
              let vtv = vty_value ?mut ~ghost ity in
              s, (create_pvsymbol fid vtv, true)
            in
            let s,pjl = Util.map_fold_left mk_field Sreg.empty fl in
            let cid = { d.td_ident with id = "mk " ^ d.td_ident.id } in
            Hashtbl.replace predefs x [Denv.create_user_id cid, pjl];
            create_itysymbol id ~abst ~priv vl (Sreg.elements s) None
        | TDalgebraic _ | TDrecord _ | TDabstract ->
            create_itysymbol id ~abst ~priv vl [] None
      in
      Hashtbl.add tysymbols x (Some ts);
      ts
  in
  Mstr.iter (fun x _ -> ignore (its_visit x)) def;

  (* create predefinitions for immutable types *)

  let def_visit d (abstr,algeb,alias) =
    let x = d.td_ident.id in
    let ts = Util.of_option (Hashtbl.find tysymbols x) in
    let add_tv s x v = Mstr.add x.id v s in
    let vars = List.fold_left2 add_tv Mstr.empty d.td_params ts.its_args in
    let get_ts = function
      | Qident { id = x } when Mstr.mem x def ->
          ProgTS (Util.of_option (Hashtbl.find tysymbols x))
      | q -> find_tysymbol q uc
    in
    let rec parse = function
      | PPTtyvar { id = v ; id_loc = loc } ->
          let e = Loc.Located (loc, UnboundTypeVar v) in
          ity_var (Mstr.find_exn e v vars)
      | PPTtyapp (tyl,q) ->
          let tyl = List.map parse tyl in
          begin match get_ts q with
            | PureTS ts -> Loc.try2 (Typing.qloc q) ity_pur ts tyl
            | ProgTS ts -> Loc.try3 (Typing.qloc q) ity_app ts tyl []
          end
      | PPTtuple tyl ->
          let ts = ts_tuple (List.length tyl) in
          ity_pur ts (List.map parse tyl)
    in
    match d.td_def with
      | TDabstract ->
          ts :: abstr, algeb, alias
      | TDalias _ ->
          abstr, algeb, ts :: alias
      | (TDalgebraic _ | TDrecord _) when Hashtbl.find mutables x ->
          abstr, (ts, Hashtbl.find predefs x) :: algeb, alias
      | TDalgebraic csl ->
          let projs = Hashtbl.create 5 in
          let mk_proj (id,pty) =
            let ity = parse pty in
            let vtv = vty_value ity in
            match id with
              | None ->
                  create_pvsymbol (id_fresh "pj") vtv, false
              | Some id ->
                  try
                    let pv = Hashtbl.find projs id.id in
                    let ty = pv.pv_vtv.vtv_ity in
                    (* once we have ghost/mutable fields in algebraics,
                       don't forget to check here that they coincide, too *)
                    Loc.try2 id.id_loc ity_equal_check ty ity;
                    pv, true
                  with Not_found ->
                    let pv = create_pvsymbol (Denv.create_user_id id) vtv in
                    Hashtbl.replace projs id.id pv;
                    pv, true
          in
          let mk_constr (_loc,cid,pjl) =
            Denv.create_user_id cid, List.map mk_proj pjl in
          abstr, (ts, List.map mk_constr csl) :: algeb, alias
      | TDrecord fl ->
          let mk_field f =
            let fid = Denv.create_user_id f.f_ident in
            let vtv = vty_value ~ghost:f.f_ghost (parse f.f_pty) in
            create_pvsymbol fid vtv, true in
          let cid = { d.td_ident with id = "mk " ^ d.td_ident.id } in
          let csl = [Denv.create_user_id cid, List.map mk_field fl] in
          abstr, (ts, csl) :: algeb, alias
  in
  let abstr,algeb,alias = List.fold_right def_visit tdl ([],[],[]) in

  (* detect pure type declarations *)

  let kn = get_known uc in
  let check its = Mid.mem its.its_pure.ts_name kn in
  let check ity = ity_s_any check Util.ffalse ity in
  let is_impure_type ts =
    ts.its_abst || ts.its_priv || ts.its_regs <> [] ||
    option_apply false check ts.its_def
  in
  let check (pv,_) =
    let vtv = pv.pv_vtv in
    vtv.vtv_ghost || vtv.vtv_mut <> None || check vtv.vtv_ity in
  let is_impure_data (ts,csl) =
    is_impure_type ts ||
    List.exists (fun (_,l) -> List.exists check l) csl
  in
  let mk_pure_decl (ts,csl) =
    let pjt = Hvs.create 3 in
    let ty = ty_app ts.its_pure (List.map ty_var ts.its_args) in
    let mk_proj (pv,f) =
      let vs = pv.pv_vs in
      if f then try vs.vs_ty, Some (Hvs.find pjt vs) with Not_found ->
        let pj = create_fsymbol (id_clone vs.vs_name) [ty] vs.vs_ty in
        Hvs.replace pjt vs pj;
        vs.vs_ty, Some pj
      else
        vs.vs_ty, None
    in
    let mk_constr (id,pjl) =
      let pjl = List.map mk_proj pjl in
      let cs = create_fsymbol id (List.map fst pjl) ty in
      cs, List.map snd pjl
    in
    ts.its_pure, List.map mk_constr csl
  in
  let add_type_decl uc ts =
    if is_impure_type ts then
      add_pdecl_with_tuples uc (create_ty_decl ts)
    else
      add_decl_with_tuples uc (Decl.create_ty_decl ts.its_pure)
  in
  try
    let uc = List.fold_left add_type_decl uc abstr in
    let uc = if algeb = [] then uc else
      if List.exists is_impure_data algeb then
        add_pdecl_with_tuples uc (create_data_decl algeb)
      else
        let d = List.map mk_pure_decl algeb in
        add_decl_with_tuples uc (Decl.create_data_decl d)
    in
    let uc = List.fold_left add_type_decl uc alias in
    uc
  with
    | ClashSymbol s ->
        error ?loc:(look_for_loc tdl s) (ClashSymbol s)
    | RecordFieldMissing ({ ls_name = { id_string = s }} as cs,ls) ->
        error ?loc:(look_for_loc tdl s) (RecordFieldMissing (cs,ls))
    | DuplicateRecordField ({ ls_name = { id_string = s }} as cs,ls) ->
        error ?loc:(look_for_loc tdl s) (DuplicateRecordField (cs,ls))
    | DuplicateVar { vs_name = { id_string = s }} ->
        errorm ?loc:(look_for_loc tdl s)
          "Field %s is used twice in the same constructor" s

(** Use/Clone of theories and modules *)

type mlw_contents = modul Mstr.t
type mlw_library = mlw_contents library
type mlw_file = mlw_contents * Theory.theory Mstr.t

let find_theory loc lib path s =
  (* search first in .mlw files (using lib) *)
  let thm =
    try Some (Env.read_lib_theory lib path s)
    with LibFileNotFound _ | TheoryNotFound _ -> None
  in
  (* search also in .why files *)
  let th =
    try Some (Env.find_theory (Env.env_of_library lib) path s)
    with LibFileNotFound _ | TheoryNotFound _ -> None
  in
  match thm, th with
    | Some _, Some _ ->
        Loc.errorm ~loc
          "a module/theory %s is defined both in Why and WhyML libraries" s
    | None, None -> Loc.error ~loc (Env.TheoryNotFound (path, s))
    | None, Some t | Some t, None -> t

let find_theory loc lib mt path s = match path with
  | [] -> (* local theory *)
      begin try Mstr.find s mt with Not_found -> find_theory loc lib [] s end
  | _ :: _ -> (* theory in file path *)
      find_theory loc lib path s

type theory_or_module = Theory of Theory.theory | Module of modul

let print_path fmt sl =
  Pp.print_list (Pp.constant_string ".") Format.pp_print_string fmt sl

let find_module loc lib path s =
  (* search first in .mlw files *)
  let m, thm =
    try
      let mm, mt = Env.read_lib_file lib path in
      Mstr.find_opt s mm, Mstr.find_opt s mt
    with
      | LibFileNotFound _ -> None, None
  in
  (* search also in .why files *)
  let th =
    try Some (Env.find_theory (Env.env_of_library lib) path s)
    with LibFileNotFound _ | TheoryNotFound _ -> None
  in
  match m, thm, th with
    | Some _, None, _ -> assert false
    | _, Some _, Some _ ->
        Loc.errorm ~loc
          "a module/theory %s is defined both in Why and WhyML libraries" s
    | None, None, None ->
        Loc.errorm ~loc "Theory/module not found: %a" print_path (path @ [s])
    | Some m, Some _, None -> Module m
    | None, Some t, None | None, None, Some t -> Theory t

let find_module loc lib mm mt path s = match path with
  | [] -> (* local module/theory *)
      begin try Module (Mstr.find s mm)
        with Not_found -> begin try Theory (Mstr.find s mt)
          with Not_found -> find_module loc lib [] s end end
  | _ :: _ -> (* module/theory in file path *)
      find_module loc lib path s

(** Main loop *)

let add_theory lib path mt m =
  let { id = id; id_loc = loc } = m.pth_name in
  if Mstr.mem id mt then Loc.errorm ~loc "clash with previous theory %s" id;
  let uc = create_theory ~path (Denv.create_user_id m.pth_name) in
  let rec add_decl uc = function
    | Dlogic d ->
        Typing.add_decl uc d
    | Duseclone (loc, use, inst) ->
        let path, s = Typing.split_qualid use.use_theory in
        let th = find_theory loc lib mt path s in
        (* open namespace, if any *)
        let uc =
          if use.use_imp_exp <> None then Theory.open_namespace uc else uc in
        (* use or clone *)
        let uc = match inst with
          | None -> Theory.use_export uc th
          | Some inst ->
              let inst = Typing.type_inst uc th inst in
              Theory.clone_export uc th inst
        in
        (* close namespace, if any *)
        begin match use.use_imp_exp with
          | None -> uc
          | Some imp -> Theory.close_namespace uc imp use.use_as
        end
    | Dnamespace (loc, name, import, dl) ->
        let uc = Theory.open_namespace uc in
        let uc = List.fold_left add_decl uc dl in
        Loc.try3 loc Theory.close_namespace uc import name
    | Dlet _ | Dletrec _ | Dparam _ | Dexn _ | Duse _ ->
        assert false
  in
  let uc = List.fold_left add_decl uc m.pth_decl in
  let th = close_theory uc in
  Mstr.add id th mt

let add_module lib path mm mt m =
  let { id = id; id_loc = loc } = m.mod_name in
  if Mstr.mem id mm then Loc.errorm ~loc "clash with previous module %s" id;
  if Mstr.mem id mt then Loc.errorm ~loc "clash with previous theory %s" id;
  let uc = create_module ~path (Denv.create_user_id m.mod_name) in
  let rec add_decl uc = function
    | Dlogic (TypeDecl tdl) ->
        add_types uc tdl
    | Dlogic d ->
        add_to_theory Typing.add_decl uc d
    | Duseclone (loc, use, inst) ->
        let path, s = Typing.split_qualid use.use_theory in
        let mth = find_module loc lib mm mt path s in
        (* open namespace, if any *)
        let uc = if use.use_imp_exp <> None then open_namespace uc else uc in
        (* use or clone *)
        let uc = match mth, inst with
          | Theory th, None -> use_export_theory uc th
          | Theory th, Some inst ->
              let inst = Typing.type_inst (get_theory uc) th inst in
              clone_export_theory uc th inst
          | Module m, None -> use_export uc m
          | Module m, Some inst ->
              let inst = Typing.type_inst (get_theory uc) m.mod_theory inst in
              clone_export uc m inst
        in
        (* close namespace, if any *)
        begin match use.use_imp_exp with
          | None -> uc
          | Some imp -> close_namespace uc imp use.use_as
        end
    | Dnamespace (loc, name, import, dl) ->
        let uc = open_namespace uc in
        let uc = List.fold_left add_decl uc dl in
        Loc.try3 loc close_namespace uc import name
    | Dlet (id, e) ->
        let e = dexpr (create_denv uc) e in
        let pd = match e.de_desc with
          | DEfun lam ->
              let def = expr_fun (create_lenv uc) id lam in
              create_rec_decl [def]
          | _ ->
              let e = expr (create_lenv uc) e in
              let def = create_let_defn (Denv.create_user_id id) e in
              create_let_decl def
        in
        Loc.try2 loc add_pdecl_with_tuples uc pd
    | Dletrec rdl ->
        let rdl = dletrec (create_denv uc) rdl in
        let rdl = expr_rec (create_lenv uc) rdl in
        let pd = create_rec_decl rdl in
        Loc.try2 loc add_pdecl_with_tuples uc pd
    | Dexn (id, pty) ->
        let ity = match pty with
          | Some pty ->
              ity_of_dity (dity_of_pty ~user:false (create_denv uc) pty)
          | None -> ity_unit in
        let xs = create_xsymbol (Denv.create_user_id id) ity in
        let pd = create_exn_decl xs in
        Loc.try2 loc add_pdecl_with_tuples uc pd
    | Dparam (id, tyv) ->
        let tyv, _ = dtype_v (create_denv uc) tyv in
        let tyv = type_v (create_lenv uc) tyv in
        let vd = create_val (Denv.create_user_id id) tyv in
        let pd = create_val_decl vd in
        Loc.try2 loc add_pdecl_with_tuples uc pd
    | Duse _ ->
        assert false (*TO BE REMOVED EVENTUALLY *)
  in
  let uc = List.fold_left add_decl uc m.mod_decl in
  let m = close_module uc in
  Mstr.add id m mm, Mstr.add id m.mod_theory mt

let add_theory_module lib path (mm, mt) = function
  | Ptheory th -> mm, add_theory lib path mt th
  | Pmodule m -> add_module lib path mm mt m

