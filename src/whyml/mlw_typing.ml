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
exception UnboundSymbol of qualid

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
      Format.fprintf fmt "Unbound type variable '%s" s
  | UnboundSymbol q ->
      Format.fprintf fmt "Unbound symbol '%a'" print_qualid q
  | _ -> raise e)

(* TODO: let type_only = Debug.test_flag Typing.debug_type_only in *)

type denv = {
  uc     : module_uc;
  locals : (tvars * dvty) Mstr.t;
  tvars  : tvars;
  uloc   : Ptree.loc option;
}

let create_denv uc = {
  uc     = uc;
  locals = Mstr.empty;
  tvars  = empty_tvars;
  uloc   = None;
}

(* Handle tuple symbols *)

let ht_tuple   = Hashtbl.create 3
let ts_tuple n = Hashtbl.replace ht_tuple n (); ts_tuple n
let fs_tuple n = Hashtbl.replace ht_tuple n (); fs_tuple n

let rec check_at f0 =
  let rec check f = match f.t_node with
    | Term.Tapp (ls, _) when ls_equal ls fs_at ->
        let d = Mvs.set_diff f.t_vars f0.t_vars in
        if not (Mvs.is_empty d) then errorm ?loc:f.t_loc
          "locally bound variable %a under `at'"
          Pretty.print_vs (fst (Mvs.choose d))
        else true
    | _ ->
        t_all check f
  in
  ignore (check f0)

let count_term_tuples t =
  let syms_ts _ ts = match is_ts_tuple_id ts.ts_name with
    | Some n -> Hashtbl.replace ht_tuple n () | _ -> () in
  let syms_ty _ ty = ty_s_fold syms_ts () ty in
  t_s_fold syms_ty (fun _ _ -> ()) () t

let flush_tuples uc =
  let kn = Theory.get_known (get_theory uc) in
  let add_tuple n _ uc =
    if Mid.mem (ts_tuple n).ts_name kn then uc
    else use_export_theory uc (tuple_theory n) in
  let uc = Hashtbl.fold add_tuple ht_tuple uc in
  Hashtbl.clear ht_tuple;
  uc

let add_pdecl_with_tuples uc pd = add_pdecl (flush_tuples uc) pd
let add_decl_with_tuples uc d = add_decl (flush_tuples uc) d

(** Namespace lookup *)

let uc_find_ls uc p =
  let x = Typing.string_list_of_qualid [] p in
  try ns_find_ls (Theory.get_namespace (get_theory uc)) x
  with Not_found -> error ~loc:(qloc p) (UnboundSymbol p)

let uc_find_ts uc p =
  let x = Typing.string_list_of_qualid [] p in
  try ns_find_ts (get_namespace uc) x
  with Not_found -> error ~loc:(qloc p) (UnboundSymbol p)

let uc_find_ps uc p =
  let x = Typing.string_list_of_qualid [] p in
  try ns_find_ps (get_namespace uc) x
  with Not_found -> error ~loc:(qloc p) (UnboundSymbol p)

(** Typing type expressions *)

let rec dity_of_pty ~user denv = function
  | Ptree.PPTtyvar id ->
      create_user_type_variable id
  | Ptree.PPTtyapp (pl, p) ->
      let dl = List.map (dity_of_pty ~user denv) pl in
      begin match uc_find_ts denv.uc p with
        | PT ts -> its_app ~user ts dl
        | TS ts -> ts_app ts dl
      end
  | Ptree.PPTtuple pl ->
      let dl = List.map (dity_of_pty ~user denv) pl in
      ts_app (ts_tuple (List.length pl)) dl

(** Typing program expressions *)

let dity_int  = ts_app ts_int  []
let dity_real = ts_app ts_real []
let dity_bool = ts_app ts_bool []
let dity_unit = ts_app ts_unit []
let dity_mark = ts_app ts_mark []

let unify_loc unify_fn loc x1 x2 = try unify_fn x1 x2 with
  | TypeMismatch (ity1,ity2) -> errorm ~loc
      "This expression has type %a, but is expected to have type %a"
      Mlw_pretty.print_ity ity2 Mlw_pretty.print_ity ity1
  | exn -> error ~loc exn

let expected_type { de_loc = loc ; de_type = (argl,res) } dity =
  if argl <> [] then errorm ~loc "This expression is not a first-order value";
  unify_loc unify loc dity res

let expected_type_weak { de_loc = loc ; de_type = (argl,res) } dity =
  if argl <> [] then errorm ~loc "This expression is not a first-order value";
  unify_loc unify_weak loc dity res

let rec extract_labels labs loc e = match e.Ptree.expr_desc with
  | Ptree.Enamed (Ptree.Lstr s, e) -> extract_labels (Slab.add s labs) loc e
  | Ptree.Enamed (Ptree.Lpos p, e) -> extract_labels labs (Some p) e
  | Ptree.Ecast  (e, ty) ->
      let labs, loc, d = extract_labels labs loc e in
      labs, loc, Ptree.Ecast ({ e with Ptree.expr_desc = d }, ty)
  | e -> labs, loc, e

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

let find_prog_field uc (p,e) = match uc_find_ps uc p with PL pl -> pl, e
  | _ -> errorm ~loc:(qloc p) "'%a' is not a record field" print_qualid p

let find_pure_field uc (p,e) = uc_find_ls uc p, e

let is_pure_record uc = function
  | fl :: _ -> (try ignore (find_prog_field uc fl); false with _ -> true)
  | [] -> raise Decl.EmptyRecord

let hidden_pl ~loc pl =
  { de_desc = DEglobal_pl pl;
    de_type = specialize_plsymbol pl;
    de_loc  = loc; de_lab = Slab.empty }

let hidden_ls ~loc ls =
  { de_desc = DEglobal_ls ls;
    de_type = specialize_lsymbol ls;
    de_loc  = loc; de_lab = Slab.empty }

(* helper functions for let-expansion *)
let test_var e = match e.de_desc with
  | DElocal _ | DEglobal_pv _ -> true
  | _ -> false

let mk_var e =
  if test_var e then e else
  { de_desc = DElocal "q";
    de_type = e.de_type;
    de_loc  = e.de_loc;
    de_lab  = Slab.empty }

let mk_id s loc =
  { id = s; id_loc = loc; id_lab = [] }

let mk_dexpr desc dvty loc labs =
  { de_desc = desc; de_type = dvty; de_loc = loc; de_lab = labs }

let mk_let ~loc ~uloc e (desc,dvty) =
  if test_var e then desc, dvty else
  let loc = def_option loc uloc in
  let e1 = mk_dexpr desc dvty loc Slab.empty in
  DElet (mk_id "q" loc, false, e, e1), dvty

(* patterns *)

let add_var id dity denv =
  let tvars = add_dity denv.tvars dity in
  let locals = Mstr.add id.id (tvars,([],dity)) denv.locals in
  { denv with locals = locals; tvars = tvars }

let specialize_qualid uc p = match uc_find_ps uc p with
  | PV pv -> DEglobal_pv pv, ([],specialize_pvsymbol pv)
  | PS ps -> DEglobal_ps ps, specialize_psymbol  ps
  | PL pl -> DEglobal_pl pl, specialize_plsymbol pl
  | LS ls -> DEglobal_ls ls, specialize_lsymbol ls
  | XS xs -> errorm ~loc:(qloc p) "unexpected exception symbol %a" print_xs xs

let find_xsymbol uc p = match uc_find_ps uc p with
  | XS xs -> xs
  | _ -> errorm ~loc:(qloc p) "exception symbol expected"

let find_variant_ls uc p = match uc_find_ls uc p with
  | { ls_args = [u;v]; ls_value = None } as ls when ty_equal u v -> ls
  | ls -> errorm ~loc:(qloc p) "%a is not a binary relation" Pretty.print_ls ls

let find_global_vs uc p = try match uc_find_ps uc p with
  | PV pv -> Some pv.pv_vs
  | _ -> None
  with _ -> None

let rec dpattern denv ({ pat_loc = loc } as pp) = match pp.pat_desc with
  | Ptree.PPpwild ->
      PPwild, create_type_variable (), denv
  | Ptree.PPpvar id ->
      let dity = create_type_variable () in
      PPvar (Denv.create_user_id id), dity, add_var id dity denv
  | Ptree.PPpapp (q,ppl) ->
      let sym, dvty = specialize_qualid denv.uc q in
      dpat_app denv loc (mk_dexpr sym dvty loc Slab.empty) ppl
  | Ptree.PPprec fl when is_pure_record denv.uc fl ->
      let kn = Theory.get_known (get_theory denv.uc) in
      let fl = List.map (find_pure_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc Decl.parse_record kn fl in
      let wild = { pat_desc = Ptree.PPpwild; pat_loc = loc } in
      let get_val pj = Mls.find_def wild pj flm in
      dpat_app denv loc (hidden_ls ~loc cs) (List.map get_val pjl)
  | Ptree.PPprec fl ->
      let fl = List.map (find_prog_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc parse_record denv.uc fl in
      let wild = { pat_desc = Ptree.PPpwild; pat_loc = loc } in
      let get_val pj = Mls.find_def wild pj.pl_ls flm in
      dpat_app denv loc (hidden_pl ~loc cs) (List.map get_val pjl)
  | Ptree.PPptuple ppl ->
      let cs = fs_tuple (List.length ppl) in
      dpat_app denv loc (hidden_ls ~loc cs) ppl
  | Ptree.PPpor (lpp1, lpp2) ->
      let pp1, dity1, denv = dpattern denv lpp1 in
      let pp2, dity2, denv = dpattern denv lpp2 in
      unify_loc unify lpp2.pat_loc dity1 dity2;
      PPor (pp1, pp2), dity1, denv
  | Ptree.PPpas (pp, id) ->
      let pp, dity, denv = dpattern denv pp in
      PPas (pp, Denv.create_user_id id), dity, add_var id dity denv

and dpat_app denv gloc ({ de_loc = loc } as de) ppl =
  let add_pp lp (ppl, tyl, denv) =
    let pp, ty, denv = dpattern denv lp in
    pp::ppl, (lp.pat_loc,ty)::tyl, denv in
  let ppl, tyl, denv = List.fold_right add_pp ppl ([],[],denv) in
  let pp, ls = match de.de_desc with
    | DEglobal_pl pl -> Mlw_expr.PPpapp (pl, ppl), pl.pl_ls
    | DEglobal_ls ls -> Mlw_expr.PPlapp (ls, ppl), ls
    | DEglobal_pv pv -> errorm ~loc "%a is not a constructor" print_pv pv
    | DEglobal_ps ps -> errorm ~loc "%a is not a constructor" print_ps ps
    | _ -> assert false
  in
  let argl, res = de.de_type in
  if List.length argl <> List.length ppl then error ~loc:gloc
    (Term.BadArity (ls, List.length argl, List.length ppl));
  let unify_arg ta (loc,tv) = unify_loc unify loc ta tv in
  List.iter2 unify_arg argl tyl;
  pp, res, denv

(* specifications *)

let dbinders denv bl =
  let hv = Hashtbl.create 3 in
  let dbinder (id,gh,pty) (denv,bl,tyl) =
    if Hashtbl.mem hv id.id then raise (DuplicateProgVar id.id);
    Hashtbl.add hv id.id ();
    let dity = match pty with
      | Some pty -> dity_of_pty ~user:true denv pty
      | None -> create_type_variable () in
    add_var id dity denv, (id,gh,dity)::bl, dity::tyl
  in
  List.fold_right dbinder bl (denv,[],[])

let deff_of_peff uc pe =
  { deff_reads  = pe.pe_reads;
    deff_writes = pe.pe_writes;
    deff_raises = List.map (fun (gh,q) -> gh, find_xsymbol uc q) pe.pe_raises; }

let dxpost uc ql = List.map (fun (q,f) -> find_xsymbol uc q, f) ql

let rec dtype_c denv tyc =
  let tyv, dvty = dtype_v denv tyc.pc_result_type in
  { dc_result = tyv;
    dc_effect = deff_of_peff denv.uc tyc.pc_effect;
    dc_pre    = tyc.pc_pre;
    dc_post   = fst tyc.pc_post;
    dc_xpost  = dxpost denv.uc (snd tyc.pc_post); },
  dvty

and dtype_v denv = function
  | Tpure pty ->
      let dity = dity_of_pty ~user:true denv pty in
      DSpecV (false,dity), ([],dity)
  | Tarrow (bl,tyc) ->
      let denv,bl,tyl = dbinders denv bl in
      let tyc,(argl,res) = dtype_c denv tyc in
      DSpecA (bl,tyc), (tyl @ argl,res)

let dvariant uc = function
  | Some (le, Some q) -> [le, Some (find_variant_ls uc q)]
  | Some (le, None) -> [le, None]
  | None -> []
(* TODO: accept a list of variants in the surface language
  List.map (fun (le,q) -> le, Util.option_map (find_variant_ls uc) q) var
*)

(* expressions *)

let de_unit ~loc = hidden_ls ~loc (Term.fs_tuple 0)

let de_app _loc e el =
  let argl, res = e.de_type in
  let rec unify_list argl el = match argl, el with
    | arg::argl, e::el when Loc.equal e.de_loc Loc.dummy_position ->
        expected_type e arg; unify_list argl el
    | arg::argl, e::el ->
        let res = unify_list argl el in expected_type e arg; res
    | argl, [] -> argl, res
    | [], _ when fst e.de_type = [] -> errorm ~loc:e.de_loc
        "This expression is not a function and cannot be applied"
    | [], _ -> errorm ~loc:e.de_loc
        "This function is applied to too many arguments"
  in
  DEapply (e, el), unify_list argl el

let rec dexpr denv e =
  let loc = e.Ptree.expr_loc in
  let labs, uloc, d = extract_labels Slab.empty denv.uloc e in
  let denv = { denv with uloc = uloc } in
  let d, ty = de_desc denv loc d in
  let loc = def_option loc uloc in
  mk_dexpr d ty loc labs

and de_desc denv loc = function
  | Ptree.Eident (Qident {id=x}) when Mstr.mem x denv.locals ->
      (* local variable *)
      let tvs, dvty = Mstr.find x denv.locals in
      let dvty = specialize_scheme tvs dvty in
      DElocal x, dvty
  | Ptree.Eident p ->
      specialize_qualid denv.uc p
  | Ptree.Eapply (e1, e2) ->
      let e, el = decompose_app [e2] e1 in
      let el = List.map (dexpr denv) el in
      de_app loc (dexpr denv e) el
  | Ptree.Elet (id, gh, e1, e2) ->
      let e1 = dexpr denv e1 in
      let dvty = e1.de_type in
      let tvars = match e1.de_desc with
        | DEfun _ -> denv.tvars
        | _ -> add_dvty denv.tvars dvty in
      let locals = Mstr.add id.id (tvars, dvty) denv.locals in
      let denv = { denv with locals = locals; tvars = tvars } in
      let e2 = dexpr denv e2 in
      DElet (id, gh, e1, e2), e2.de_type
  | Ptree.Eletrec (rdl, e1) ->
      let rdl = dletrec denv rdl in
      let add_one denv (_, { id = id }, _, dvty, _) =
        { denv with locals = Mstr.add id (denv.tvars, dvty) denv.locals } in
      let denv = List.fold_left add_one denv rdl in
      let e1 = dexpr denv e1 in
      DEletrec (rdl, e1), e1.de_type
  | Ptree.Efun (bl, tr) ->
      let denv, bl, tyl = dbinders denv bl in
      let lam, (argl, res) = dlambda denv bl None tr in
      DEfun lam, (tyl @ argl, res)
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
      DElet (mk_id "_" loc, false, e1, e2), e2.de_type
  | Ptree.Eif (e1, e2, e3) ->
      let e1 = dexpr denv e1 in
      expected_type e1 dity_bool;
      let e2 = dexpr denv e2 in
      let e3 = dexpr denv e3 in
      let res = create_type_variable () in
      expected_type e2 res;
      expected_type e3 res;
      DEif (e1, e2, e3), e2.de_type
  | Ptree.Etuple el ->
      let ls = fs_tuple (List.length el) in
      let el = List.map (dexpr denv) el in
      de_app loc (hidden_ls ~loc ls) el
  | Ptree.Erecord fl when is_pure_record denv.uc fl ->
      let kn = Theory.get_known (get_theory denv.uc) in
      let fl = List.map (find_pure_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc Decl.parse_record kn fl in
      let get_val pj = match Mls.find_opt pj flm with
        | Some e -> dexpr denv e
        | None -> error ~loc (Decl.RecordFieldMissing (cs,pj)) in
      de_app loc (hidden_ls ~loc cs) (List.map get_val pjl)
  | Ptree.Erecord fl ->
      let fl = List.map (find_prog_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc parse_record denv.uc fl in
      let get_val pj = match Mls.find_opt pj.pl_ls flm with
        | Some e -> dexpr denv e
        | None -> error ~loc (Decl.RecordFieldMissing (cs.pl_ls,pj.pl_ls)) in
      de_app loc (hidden_pl ~loc cs) (List.map get_val pjl)
  | Ptree.Eupdate (e1, fl) when is_pure_record denv.uc fl ->
      let e1 = dexpr denv e1 in
      let e0 = mk_var e1 in
      let kn = Theory.get_known (get_theory denv.uc) in
      let fl = List.map (find_pure_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc Decl.parse_record kn fl in
      let get_val pj = match Mls.find_opt pj flm with
        | Some e -> dexpr denv e
        | None ->
            let loc = Loc.dummy_position in
            let d, dvty = de_app loc (hidden_ls ~loc pj) [e0] in
            mk_dexpr d dvty loc Slab.empty in
      let res = de_app loc (hidden_ls ~loc cs) (List.map get_val pjl) in
      mk_let ~loc ~uloc:denv.uloc e1 res
  | Ptree.Eupdate (e1, fl) ->
      let e1 = dexpr denv e1 in
      let e0 = mk_var e1 in
      let fl = List.map (find_prog_field denv.uc) fl in
      let cs,pjl,flm = Loc.try2 loc parse_record denv.uc fl in
      let get_val pj = match Mls.find_opt pj.pl_ls flm with
        | Some e -> dexpr denv e
        | None ->
            let loc = Loc.dummy_position in
            let d, dvty = de_app loc (hidden_pl ~loc pj) [e0] in
            mk_dexpr d dvty loc Slab.empty in
      let res = de_app loc (hidden_pl ~loc cs) (List.map get_val pjl) in
      mk_let ~loc ~uloc:denv.uloc e1 res
  | Ptree.Eassign (e1, q, e2) ->
      let fl = { expr_desc = Eident q; expr_loc = loc } in
      let e1 = { expr_desc = Eapply (fl,e1); expr_loc = loc } in
      let e1 = dexpr denv e1 in
      let e2 = dexpr denv e2 in
      let res = create_type_variable () in
      expected_type e1 res;
      expected_type_weak e2 res;
      DEassign (e1, e2), ([], dity_unit)
  | Ptree.Econstant (ConstInt _ as c) ->
      DEconstant c, ([], dity_int)
  | Ptree.Econstant (ConstReal _ as c) ->
      DEconstant c, ([], dity_real)
  | Ptree.Enot e1 ->
      let e1 = dexpr denv e1 in
      expected_type e1 dity_bool;
      DEnot e1, ([], dity_bool)
  | Ptree.Elazy (op, e1, e2) ->
      let e1 = dexpr denv e1 in
      let e2 = dexpr denv e2 in
      expected_type e1 dity_bool;
      expected_type e2 dity_bool;
      DElazy (op, e1, e2), ([], dity_bool)
  | Ptree.Ematch (e1, bl) ->
      let e1 = dexpr denv e1 in
      let ety = create_type_variable () in
      let res = create_type_variable () in
      expected_type e1 ety;
      let branch (pp,e) =
        let ppat, dity, denv = dpattern denv pp in
        unify_loc unify pp.pat_loc ety dity;
        let e = dexpr denv e in
        expected_type e res;
        ppat, e in
      DEmatch (e1, List.map branch bl), ([], res)
  | Ptree.Eraise (q, e1) ->
      let xs = find_xsymbol denv.uc q in
      let dity = specialize_xsymbol xs in
      let e1 = match e1 with
        | Some e1 -> dexpr denv e1
        | None when ity_equal xs.xs_ity ity_unit -> de_unit ~loc
        | _ -> errorm ~loc "exception argument expected" in
      expected_type e1 dity;
      DEraise (xs, e1), ([], create_type_variable ())
  | Ptree.Etry (e1, cl) ->
      let res = create_type_variable () in
      let e1 = dexpr denv e1 in
      expected_type e1 res;
      let branch (q, id, e) =
        let xs = find_xsymbol denv.uc q in
        let dity = specialize_xsymbol xs in
        let id, denv = match id with
          | Some id -> id, add_var id dity denv
          | None -> mk_id "void" loc, denv in
        let e = dexpr denv e in
        expected_type e res;
        xs, id, e
      in
      let cl = List.map branch cl in
      DEtry (e1, cl), e1.de_type
  | Ptree.Eabsurd ->
      DEabsurd, ([], create_type_variable ())
  | Ptree.Eassert (ak, lexpr) ->
      DEassert (ak, lexpr), ([], dity_unit)
  | Ptree.Emark (id, e1) ->
      let e1 = dexpr denv e1 in
      DEmark (id, e1), e1.de_type
  | Ptree.Eany tyc ->
      let tyc, dvty = dtype_c denv tyc in
      DEany tyc, dvty
  | Ptree.Eghost e1 ->
      let e1 = dexpr denv e1 in
      DEghost e1, e1.de_type
  | Ptree.Eabstract (e1, (q,xq)) ->
      let e1 = dexpr denv e1 in
      let xq = dxpost denv.uc xq in
      DEabstract (e1, q, xq), e1.de_type
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

and dletrec denv rdl =
  (* add all functions into the environment *)
  let add_one denv (_,id,_,bl,_,_) =
    let argl = List.map (fun _ -> create_type_variable ()) bl in
    let dvty = argl, create_type_variable () in
    let tvars = add_dvty denv.tvars dvty in
    let locals = Mstr.add id.id (tvars, dvty) denv.locals in
    { denv with locals = locals; tvars = tvars }, dvty in
  let denv, dvtyl = Util.map_fold_left add_one denv rdl in
  (* then unify the binders *)
  let bind_one (_,_,_,bl,_,_) (argl,res) =
    let denv,bl,tyl = dbinders denv bl in
    List.iter2 unify argl tyl;
    denv,bl,tyl,res in
  let denvl = List.map2 bind_one rdl dvtyl in
  (* then type-check the bodies *)
  let type_one (loc, id, gh, _, var, tr) (denv,bl,tyl,tyv) =
    let lam, (argl, res) = dlambda denv bl var tr in
    if argl <> [] then errorm ~loc
      "The body of a recursive function must be a first-order value";
    unify_loc unify loc tyv res;
    loc, id, gh, (tyl, tyv), lam in
  List.map2 type_one rdl denvl

and dlambda denv bl var (p, e, (q, xq)) =
  let e = dexpr denv e in
  let var = dvariant denv.uc var in
  let xq = dxpost denv.uc xq in
  (bl, var, p, e, q, xq), e.de_type

(** stage 2 *)

type lenv = {
  mod_uc   : module_uc;
  th_at    : Theory.theory_uc;
  th_old   : Theory.theory_uc;
  let_vars : let_sym Mstr.t;
  log_vars : vsymbol Mstr.t;
  log_denv : Typing.denv;
}

let create_lenv uc = {
  mod_uc   = uc;
  th_at    = Theory.use_export (get_theory uc) Mlw_wp.th_mark_at;
  th_old   = Theory.use_export (get_theory uc) Mlw_wp.th_mark_old;
  let_vars = Mstr.empty;
  log_vars = Mstr.empty;
  log_denv = Typing.denv_empty_with_globals (find_global_vs uc);
}

let rec dty_of_ty ty = match ty.ty_node with
  | Ty.Tyapp (ts, tyl) -> Denv.tyapp ts (List.map dty_of_ty tyl)
  | Ty.Tyvar v -> Denv.tyuvar v

let create_post lenv x ty f =
  let res = create_vsymbol (id_fresh x) ty in
  let log_vars = Mstr.add x res lenv.log_vars in
  let log_denv = Typing.add_var x (dty_of_ty ty) lenv.log_denv in
  let f = Typing.type_fmla lenv.th_old log_denv log_vars f in
  let f = remove_old f in
  count_term_tuples f;
  check_at f;
  create_post res f

let create_xpost lenv x xs f = create_post lenv x (ty_of_ity xs.xs_ity) f
let create_post lenv x vty f = create_post lenv x (ty_of_vty vty) f

let create_pre lenv f =
  let f = Typing.type_fmla lenv.th_at lenv.log_denv lenv.log_vars f in
  count_term_tuples f;
  check_at f;
  f

let create_variant lenv (t,r) =
  let t = Typing.type_term lenv.th_at lenv.log_denv lenv.log_vars t in
  count_term_tuples t;
  check_at t;
  t, r

let add_local x lv lenv = match lv with
  | LetA _ ->
      { lenv with let_vars = Mstr.add x lv lenv.let_vars }
  | LetV pv ->
      let dty = dty_of_ty pv.pv_vs.vs_ty in
      { lenv with
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
    let f = create_xpost lenv "result" xs f in
    Mexn.add_new (DuplicateException xs) xs f m in
  List.fold_left add_exn Mexn.empty xq

(* add dummy postconditions for uncovered exceptions *)
let complete_xpost lenv eff xq =
  let xq = xpost lenv xq in
  let dummy { xs_ity = ity } () =
    let v = create_vsymbol (id_fresh "dummy") (ty_of_ity ity) in
    Mlw_ty.create_post v t_true in
  let xs = Sexn.union eff.eff_raises eff.eff_ghostx in
  Mexn.set_union xq (Mexn.mapi dummy (Mexn.set_diff xs xq))

(* TODO: devise a good grammar for effect expressions *)
let rec get_eff_expr lenv { pp_desc = d; pp_loc = loc } = match d with
  | Ptree.PPvar (Ptree.Qident {id=x}) when Mstr.mem x lenv.let_vars ->
      begin match Mstr.find x lenv.let_vars with
        | LetV pv -> pv.pv_vs, pv.pv_vtv
        | LetA _ -> errorm ~loc "'%s' must be a first-order value" x
      end
  | Ptree.PPvar p ->
      begin match uc_find_ps lenv.mod_uc p with
        | PV pv -> pv.pv_vs, pv.pv_vtv
        | _ -> errorm ~loc:(qloc p) "'%a' must be a variable" print_qualid p
      end
  | Ptree.PPapp (p, [le]) ->
      let vs, vtv = get_eff_expr lenv le in
      let quit () = errorm ~loc:le.pp_loc "This expression is not a record" in
      let pjm = match vtv.vtv_ity.ity_node with
        | Ityapp (its,_,_) ->
            let pjl = match find_constructors (get_known lenv.mod_uc) its with
              | (_,pjl)::_ -> pjl | _ -> quit () in
            let add_pj m pj = match pj with
              | Some { pl_ls = ls; pl_args = [vtva]; pl_value = vtvv } ->
                  Mls.add ls (vtva.vtv_ity, vtvv) m
              | Some _ -> assert false
              | None -> m in
            List.fold_left add_pj Mls.empty pjl
        | Itypur (ts,_) ->
            let kn = Theory.get_known (get_theory lenv.mod_uc) in
            let pjl = match Decl.find_constructors kn ts with
              | (_,pjl)::_ -> pjl | _ -> quit () in
            let add_pj m pj = match pj with
              | Some ({ ls_args = [tya]; ls_value = Some tyv } as ls) ->
                  Mls.add ls (ity_of_ty tya, vty_value (ity_of_ty tyv)) m
              | Some _ -> assert false
              | None -> m in
            List.fold_left add_pj Mls.empty pjl
        | _ -> quit ()
      in
      let itya, vtvv =
        try Mls.find (uc_find_ls lenv.mod_uc p) pjm with Not_found ->
          errorm ~loc:(qloc p) "'%a' must be a field name" print_qualid p in
      let sbs = unify_loc (ity_match ity_subst_empty) loc itya vtv.vtv_ity in
      let mut = Util.option_map (reg_full_inst sbs) vtvv.vtv_mut in
      let ghost = vtv.vtv_ghost || vtvv.vtv_ghost in
      vs, vty_value ~ghost ?mut (ity_full_inst sbs vtvv.vtv_ity)
  | Ptree.PPcast (e,_) | Ptree.PPnamed (_,e) ->
      get_eff_expr lenv e
  | _ ->
      errorm ~loc "unsupported effect expression"

let get_eff_regs lenv fn (eff,svs) ghost le =
  let vs, vtv = get_eff_expr lenv le in
  let ghost = ghost || vtv.vtv_ghost in
  match vtv.vtv_mut, vtv.vtv_ity.ity_node with
  | Some reg, _ ->
      fn eff ?ghost:(Some ghost) reg, Svs.add vs svs
  | None, Ityapp (its,_,(_::_ as regl)) ->
      let add_arg regs vtv = match vtv.vtv_mut with
        | Some r when vtv.vtv_ghost -> Sreg.add r regs | _ -> regs in
      let add_cs regs (cs,_) = List.fold_left add_arg regs cs.pl_args in
      let csl = find_constructors (get_known lenv.mod_uc) its in
      let ghost_regs = List.fold_left add_cs Sreg.empty csl in
      let add_reg eff reg0 reg =
        let ghost = ghost || Sreg.mem reg0 ghost_regs in
        fn eff ?ghost:(Some ghost) reg
      in
      List.fold_left2 add_reg eff its.its_regs regl, Svs.add vs svs
  | _ ->
      errorm ~loc:le.pp_loc "mutable expression expected"

let eff_of_deff lenv deff =
  let acc = eff_empty, Svs.empty in
  let add_read acc (gh,e) = get_eff_regs lenv eff_read acc gh e in
  let acc = List.fold_left add_read acc deff.deff_reads in
  let add_write acc (gh,e) = get_eff_regs lenv eff_write acc gh e in
  let eff, svs = List.fold_left add_write acc deff.deff_writes in
  let add_raise eff (gh,xs) = eff_raise eff ~ghost:gh xs in
  let eff = List.fold_left add_raise eff deff.deff_raises in
  eff, svs

let rec type_c lenv gh svs vars dtyc =
  let vty = type_v lenv gh svs vars dtyc.dc_result in
  let eff, esvs = eff_of_deff lenv dtyc.dc_effect in
  (* reset every new region in the result *)
  let eff = match vty with
    | VTvalue v ->
        let rec add_reg r eff =
          if reg_occurs r vars then eff else eff_reset (add_ity r.reg_ity eff) r
        and add_ity ity eff = Sreg.fold add_reg ity.ity_vars.vars_reg eff in
        add_ity v.vtv_ity eff
    | VTarrow _ -> eff in
  (* refresh every unmodified subregion of a modified region *)
  let writes = Sreg.union eff.eff_writes eff.eff_ghostw in
  let check u eff =
    let rec sub_reg r eff =
      if Sreg.mem r writes then eff else sub_vars r (eff_refresh eff r u)
    and sub_vars r eff = Sreg.fold sub_reg r.reg_ity.ity_vars.vars_reg eff in
    sub_vars u eff in
  let eff = Sreg.fold check writes eff in
  (* create the spec *)
  let spec = {
    c_pre     = create_pre lenv dtyc.dc_pre;
    c_effect  = eff;
    c_post    = create_post lenv "result" vty dtyc.dc_post;
    c_xpost   = complete_xpost lenv eff dtyc.dc_xpost;
    c_variant = [];
    c_letrec  = 0 } in
  (* we add an exception postcondition for %Exit that mentions
     every external variable in effect expressions which also
     does not occur in pre/post/xpost. In this way, we keep
     the variable in the specification in order to preserve
     the effect in [Mlw_ty.spec_filter]. The exception %Exit
     cannot be raised by an abstract parameter, so this xpost
     will never appear in WP *)
  let esvs = Svs.diff esvs svs in
  let drop _ t s = Mvs.set_diff s t.t_vars in
  let esvs = drop () spec.c_pre esvs in
  let esvs = drop () spec.c_post esvs in
  let esvs = Mexn.fold drop spec.c_xpost esvs in
  let xpost = if Svs.is_empty esvs then spec.c_xpost else
    let exn = Invalid_argument "Mlw_typing.type_c" in
    let res = create_vsymbol (id_fresh "dummy") ty_unit in
    let add vs f = let t = t_var vs in t_and_simp (t_equ t t) f in
    let xq = Mlw_ty.create_post res (Svs.fold add esvs t_true) in
    Mexn.add_new exn xs_exit xq spec.c_xpost in
  { spec with c_xpost = xpost }, vty

and type_v lenv gh svs vars = function
  | DSpecV (ghost,v) ->
      let ghost = ghost || gh in
      VTvalue (vty_value ~ghost (ity_of_dity v))
  | DSpecA (bl,tyc) ->
      let lenv, pvl = binders lenv bl in
      let add_pv (vars,svs) pv =
        vars_union vars pv.pv_vtv.vtv_vars, Svs.add pv.pv_vs svs in
      let vars, svs = List.fold_left add_pv (vars,svs) pvl in
      let spec, vty = type_c lenv gh svs vars tyc in
      VTarrow (vty_arrow pvl ~spec vty)

(* expressions *)

let vty_ghostify gh vty =
  if gh && not (vty_ghost vty) then vty_ghostify vty else vty

let e_ghostify gh e =
  if gh && not (vty_ghost e.e_vty) then e_ghost e else e

let rec expr lenv de =
  let loc = de.de_loc in
  let e = Loc.try3 loc expr_desc lenv loc de in
  e_label ~loc de.de_lab e

and expr_desc lenv loc de = match de.de_desc with
  | DElocal x ->
      assert (Mstr.mem x lenv.let_vars);
      begin match Mstr.find x lenv.let_vars with
      | LetV pv -> e_value pv
      | LetA ps ->
          begin match vty_of_dvty de.de_type with
            | VTarrow vta -> e_arrow ps vta
            | VTvalue _ -> assert false
          end
      end
  | DElet (x, gh, { de_desc = DEfun lam }, de2) ->
      let def, ps = expr_fun lenv x gh lam in
      let lenv = add_local x.id (LetA ps) lenv in
      let e2 = expr lenv de2 in
      e_rec def e2
  | DEfun lam ->
      let x = mk_id "fn" loc in
      let def, ps = expr_fun lenv x false lam in
      let e2 = e_arrow ps ps.ps_vta in
      e_rec def e2
  (* FIXME? (ghost "lab" fun x -> ...) loses the label "lab" *)
  | DEghost { de_desc = DEfun lam } ->
      let x = mk_id "fn" loc in
      let def, ps = expr_fun lenv x true lam in
      let e2 = e_arrow ps ps.ps_vta in
      e_rec def e2
  | DElet (x, gh, de1, de2) ->
      let e1 = e_ghostify gh (expr lenv de1) in
      let mk_expr e1 =
        let def1 = create_let_defn (Denv.create_user_id x) e1 in
        let lenv = add_local x.id def1.let_sym lenv in
        let e2 = expr lenv de2 in
        e_let def1 e2 in
      let rec flatten e1 = match e1.e_node with
        | Elet (ld,e1) -> e_let ld (flatten e1)
        | _ -> mk_expr e1 in
      begin match e1.e_vty with
        | VTarrow { vta_ghost = true } when not gh ->
            errorm ~loc "%s must be a ghost function" x.id
        | VTarrow _ -> flatten e1
        | VTvalue _ -> mk_expr e1
      end;
  | DEletrec (rdl, de1) ->
      let rdl = expr_rec lenv rdl in
      let add_rd { fun_ps = ps } = add_local ps.ps_name.id_string (LetA ps) in
      let e1 = expr (List.fold_right add_rd rdl.rec_defn lenv) de1 in
      e_rec rdl e1
  | DEapply (de1, del) ->
      let el = List.map (expr lenv) del in
      begin match de1.de_desc with
        | DEglobal_pl pls -> e_plapp pls el (ity_of_dity (snd de.de_type))
        | DEglobal_ls ls  -> e_lapp  ls  el (ity_of_dity (snd de.de_type))
        | _               -> e_app (expr lenv de1) el
      end
  | DEglobal_pv pv ->
      e_value pv
  | DEglobal_ps ps ->
      begin match vty_of_dvty de.de_type with
        | VTarrow vta -> e_arrow ps vta
        | VTvalue _ -> assert false
      end
  | DEglobal_pl pl ->
      e_plapp pl [] (ity_of_dity (snd de.de_type))
  | DEglobal_ls ls ->
      e_lapp ls [] (ity_of_dity (snd de.de_type))
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
  | DEabstract (de1, q, xq) ->
      let e1 = expr lenv de1 in
      let q = create_post lenv "result" e1.e_vty q in
      e_abstract e1 q (complete_xpost lenv e1.e_effect xq)
  | DEassert (ak, f) ->
      let ak = match ak with
        | Ptree.Aassert -> Aassert
        | Ptree.Aassume -> Aassume
        | Ptree.Acheck  -> Acheck in
      e_assert ak (create_pre lenv f)
  | DEabsurd ->
      e_absurd (ity_of_dity (snd de.de_type))
  | DEraise (xs, de1) ->
      e_raise xs (expr lenv de1) (ity_of_dity (snd de.de_type))
  | DEtry (de1, bl) ->
      let e1 = expr lenv de1 in
      let branch (xs,id,de) =
        let vtv = vty_value xs.xs_ity in
        let pv = create_pvsymbol (Denv.create_user_id id) vtv in
        let lenv = add_local id.id (LetV pv) lenv in
        xs, pv, expr lenv de in
      e_try e1 (List.map branch bl)
  (* We push ghost down in order to safely capture even non-ghost
     raises of the inner expression in "ghost try e1 with ..." *)
  | DEghost ({ de_desc = DEtry (de2, bl) } as de1) ->
      let de2 = { de1 with de_desc = DEghost de2 } in
      expr lenv { de1 with de_desc = DEtry (de2, bl) }
  | DEmark (x, de1) ->
      let ld = create_let_defn (Denv.create_user_id x) e_now in
      let lenv = add_local x.id ld.let_sym lenv in
      e_let ld (expr lenv de1)
  | DEany dtyc ->
      let spec, result = type_c lenv false Svs.empty vars_empty dtyc in
      e_any spec result
  | DEghost de1 ->
      e_ghostify true (expr lenv de1)
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
  let step1 lenv (_loc, id, gh, dvty, lam) =
    let vta = match vty_ghostify gh (vty_of_dvty dvty) with
      | VTarrow vta -> vta
      | VTvalue _ -> assert false in
    let ps = create_psymbol (Denv.create_user_id id) vta in
    add_local id.id (LetA ps) lenv, (ps, gh, lam) in
  let lenv, rdl = Util.map_fold_left step1 lenv rdl in
  let step2 (ps, gh, lam) = ps, expr_lam lenv gh lam in
  create_rec_defn (List.map step2 rdl)

and expr_fun lenv x gh lam =
  let lam = expr_lam lenv gh lam in
  let def = create_fun_defn (Denv.create_user_id x) lam in
  def, (List.hd def.rec_defn).fun_ps

and expr_lam lenv gh (bl, var, p, de, q, xq) =
  let lenv, pvl = binders lenv bl in
  let e = e_ghostify gh (expr lenv de) in
  if not gh && vty_ghost e.e_vty then
    errorm ~loc:de.de_loc "ghost body in a non-ghost function";
  { l_args = pvl;
    l_variant = List.map (create_variant lenv) var;
    l_pre = create_pre lenv p;
    l_expr = e;
    l_post = create_post lenv "result" e.e_vty q;
    l_xpost = complete_xpost lenv e.e_effect xq }

(** Type declaration *)

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
            begin match uc_find_ts uc q with
              | PT its -> its.its_regs <> []
              | TS _ -> false
            end
      in
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
        | Qident { id = x } when Mstr.mem x def -> PT (its_visit x)
        | q -> uc_find_ts uc q
      in
      let rec parse = function
        | PPTtyvar { id = v ; id_loc = loc } ->
            let e = Loc.Located (loc, UnboundTypeVar v) in
            ity_var (Mstr.find_exn e v vars)
        | PPTtyapp (tyl,q) ->
            let tyl = List.map parse tyl in
            begin match get_ts q with
              | TS ts -> Loc.try2 (qloc q) ity_pur ts tyl
              | PT ts -> Loc.try2 (qloc q) ity_app_fresh ts tyl
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
                      (* TODO: once we have ghost/mutable fields in algebraics,
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
          PT (Util.of_option (Hashtbl.find tysymbols x))
      | q -> uc_find_ts uc q
    in
    let rec parse = function
      | PPTtyvar { id = v ; id_loc = loc } ->
          let e = Loc.Located (loc, UnboundTypeVar v) in
          ity_var (Mstr.find_exn e v vars)
      | PPTtyapp (tyl,q) ->
          let tyl = List.map parse tyl in
          begin match get_ts q with
            | TS ts -> Loc.try2 (qloc q) ity_pur ts tyl
            | PT ts -> Loc.try3 (qloc q) ity_app ts tyl []
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
  (* search first in .mlw files or among the built-ins *)
  let thm =
    try Some (Env.read_lib_theory lib path s)
    with LibFileNotFound _ | TheoryNotFound _ -> None
  in
  (* search also in .why files, unless the theory is built-in *)
  let th =
    if path = [] then None else
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
  let rec add_pure_decl uc (loc,decl) = Loc.try3 loc real_add uc loc decl
  and real_add uc loc decl = match decl with
    | Dlogic d ->
        Typing.add_decl uc d
    | Duseclone (use, inst) ->
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
    | Dnamespace (name, import, dl) ->
        let uc = Theory.open_namespace uc in
        let uc = List.fold_left add_pure_decl uc dl in
        Theory.close_namespace uc import name
    | Dlet _ | Dletrec _ | Dparam _ | Dexn _ | Duse _ ->
        assert false
  in
  let uc = List.fold_left add_pure_decl uc m.pth_decl in
  let th = close_theory uc in
  Mstr.add id th mt

let add_module lib path mm mt m =
  let { id = id; id_loc = loc } = m.mod_name in
  if Mstr.mem id mm then Loc.errorm ~loc "clash with previous module %s" id;
  if Mstr.mem id mt then Loc.errorm ~loc "clash with previous theory %s" id;
  let env = Env.env_of_library lib in
  let uc = create_module env ~path (Denv.create_user_id m.mod_name) in
  let rec add_prog_decl uc (loc,decl) = Loc.try3 loc real_add uc loc decl
  and real_add uc loc decl = match decl with
    | Dlogic (TypeDecl tdl) ->
        add_types uc tdl
    | Dlogic d ->
        let th0 = get_theory uc in
        let dl0 = get_rev_decls th0 in
        let seen td = match dl0 with
          | td0 :: _ -> td_equal td td0
          | [] -> false in
        (* we extract the added declarations and readd it to uc *)
        let rec add_td uc = function
          | [] -> uc
          | td :: _ when seen td -> uc
          | { td_node = Theory.Decl d } :: dl ->
              add_decl (add_td uc dl) d
          | { td_node = Theory.Meta (m,al) } :: dl ->
              add_meta (add_td uc dl) m al
          | { td_node = Theory.Use th } :: dl ->
              use_export_theory (add_td uc dl) th
          | { td_node = Theory.Clone _ } :: _ -> assert false in
        add_td uc (get_rev_decls (Typing.add_decl th0 d))
    | Duseclone (use, inst) ->
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
    | Dnamespace (name, import, dl) ->
        let uc = open_namespace uc in
        let uc = List.fold_left add_prog_decl uc dl in
        close_namespace uc import name
    | Dlet (id, gh, e) ->
        let e = dexpr (create_denv uc) e in
        let pd = match e.de_desc with
          | DEfun lam ->
              let def, _ = expr_fun (create_lenv uc) id gh lam in
              create_rec_decl def
          | _ ->
              let e = e_ghostify gh (expr (create_lenv uc) e) in
              if not gh && vty_ghost e.e_vty then
                errorm ~loc "%s must be a ghost variable" id.id;
              let def = create_let_defn (Denv.create_user_id id) e in
              create_let_decl def
        in
        add_pdecl_with_tuples uc pd
    | Dletrec rdl ->
        let rdl = dletrec (create_denv uc) rdl in
        let rdl = expr_rec (create_lenv uc) rdl in
        let pd = create_rec_decl rdl in
        add_pdecl_with_tuples uc pd
    | Dexn (id, pty) ->
        let ity = match pty with
          | Some pty ->
              ity_of_dity (dity_of_pty ~user:false (create_denv uc) pty)
          | None -> ity_unit in
        let xs = create_xsymbol (Denv.create_user_id id) ity in
        let pd = create_exn_decl xs in
        add_pdecl_with_tuples uc pd
    | Dparam (id, gh, tyv) ->
        let tyv, _ = dtype_v (create_denv uc) tyv in
        let tyv = type_v (create_lenv uc) gh Svs.empty vars_empty tyv in
        let vd = create_val (Denv.create_user_id id) tyv in
        begin match vd.val_sym with
          | LetA { ps_vta = { vta_ghost = true }} when not gh ->
              errorm ~loc "%s must be a ghost function" id.id
          | LetV { pv_vtv = { vtv_ghost = true }} when not gh ->
              errorm ~loc "%s must be a ghost variable" id.id
          | _ -> ()
        end;
        let pd = create_val_decl vd in
        add_pdecl_with_tuples uc pd
    (* TODO: this is made obsolete by Duseclone, remove later *)
    | Duse (qid, use_imp_exp, use_as) ->
        let path, s = Typing.split_qualid qid in
        let mth = find_module loc lib mm mt path s in
        (* open namespace, if any *)
        let uc = if use_imp_exp <> None then open_namespace uc else uc in
        (* use or clone *)
        let uc = match mth with
          | Theory _ -> errorm ~loc "Module not found: %a" print_qualid qid
          | Module m -> use_export uc m
        in
        (* close namespace, if any *)
        begin match use_imp_exp with
          | None -> uc
          | Some imp -> close_namespace uc imp use_as
        end
  in
  let uc = List.fold_left add_prog_decl uc m.mod_decl in
  let m = close_module uc in
  Mstr.add id m mm, Mstr.add id m.mod_theory mt

let add_theory_module lib path (mm, mt) = function
  | Ptheory th -> mm, add_theory lib path mt th
  | Pmodule m -> add_module lib path mm mt m

