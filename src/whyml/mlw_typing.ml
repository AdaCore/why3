(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2012   --   INRIA - CNRS - Paris-Sud University  *)
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
  | TooLateInvariant ->
      Format.fprintf fmt
        "Cannot add a type invariant after another program declaration"
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
let implicit_post = Debug.register_flag "implicit_post"
  ~desc:"Generate@ a@ postcondition@ for@ pure@ functions@ without@ one."

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

let ht_tuple   = Hint.create 3
let ts_tuple n = Hint.replace ht_tuple n (); ts_tuple n
let fs_tuple n = Hint.replace ht_tuple n (); fs_tuple n

let check_at f0 =
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
    | Some n -> Hint.replace ht_tuple n () | _ -> () in
  let syms_ty _ ty = ty_s_fold syms_ts () ty in
  t_s_fold syms_ty (fun _ _ -> ()) () t

let flush_tuples uc =
  let kn = Theory.get_known (get_theory uc) in
  let add_tuple n _ uc =
    if Mid.mem (Ty.ts_tuple n).ts_name kn then uc
    else use_export_theory uc (tuple_theory n) in
  let uc = Hint.fold add_tuple ht_tuple uc in
  Hint.clear ht_tuple;
  uc

let add_pdecl_with_tuples ~wp uc pd = add_pdecl ~wp (flush_tuples uc) pd
let add_decl_with_tuples uc d = add_decl (flush_tuples uc) d

(** Namespace lookup *)

let uc_find_ls uc p =
  let ns = Theory.get_namespace (get_theory uc) in
  Typing.find_ns (fun ls -> ls.ls_name) Theory.ns_find_ls p ns

let get_id_ts = function
  | PT pt -> pt.its_pure.ts_name
  | TS ts -> ts.ts_name

let uc_find_ts uc p =
  Typing.find_ns get_id_ts ns_find_ts p (get_namespace uc)

let get_id_ps = function
  | PV pv -> pv.pv_vs.vs_name
  | PS ps -> ps.ps_name
  | PL pl -> pl.pl_ls.ls_name
  | XS xs -> xs.xs_name
  | LS ls -> ls.ls_name

let uc_find_ps uc p =
  Typing.find_ns get_id_ps ns_find_ps p (get_namespace uc)

(** Typing type expressions *)

let rec dity_of_pty denv = function
  | Ptree.PPTtyvar id ->
      create_user_type_variable id
  | Ptree.PPTtyapp (pl, p) ->
      let dl = List.map (dity_of_pty denv) pl in
      begin match uc_find_ts denv.uc p with
        | PT ts -> its_app ts dl
        | TS ts -> ts_app ts dl
      end
  | Ptree.PPTtuple pl ->
      let dl = List.map (dity_of_pty denv) pl in
      ts_app (ts_tuple (List.length pl)) dl

(** Typing program expressions *)

let dity_int  = ts_app ts_int  []
let dity_real = ts_app ts_real []
let dity_bool = ts_app ts_bool []
let dity_unit = ts_app ts_unit []
(* dead code
let dity_mark = ts_app ts_mark []
*)

let unify_loc unify_fn loc x1 x2 = try unify_fn x1 x2 with
  | TypeMismatch (ity1,ity2,_) -> errorm ~loc
      "This expression has type %a,@ but is expected to have type %a"
      Mlw_pretty.print_ity ity2 Mlw_pretty.print_ity ity1
  | DTypeMismatch (dity1,dity2) -> errorm ~loc
      "This expression has type %a,@ but is expected to have type %a"
      Mlw_dty.print_dity dity2 Mlw_dty.print_dity dity1
  | exn when Debug.nottest_flag Debug.stack_trace -> error ~loc exn

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
    | [cs,pjl] -> cs, List.map (Opt.get_exn (BadRecordField pl.pl_ls)) pjl
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
  let loc = Opt.get_def loc uloc in
  let e1 = mk_dexpr desc dvty loc Slab.empty in
  DElet (mk_id "q" e.de_loc, false, e, e1), dvty

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

let find_vs uc lvm p = match p with
  | Qdot _ -> find_global_vs uc p
  | Qident id ->
      let ovs = Mstr.find_opt id.id lvm in
      if ovs = None then find_global_vs uc p else ovs

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
  let hv = Hstr.create 3 in
  let dbinder (id,gh,pty) (denv,bl,tyl) =
    if Hstr.mem hv id.id then raise (DuplicateProgVar id.id);
    Hstr.add hv id.id ();
    let dity = match pty with
      | Some pty -> dity_of_pty denv pty
      | None -> create_type_variable () in
    add_var id dity denv, (id,gh,dity)::bl, dity::tyl
  in
  List.fold_right dbinder bl (denv,[],[])

let mk_dpost loc = function
  | [{ pat_desc = PPpwild | PPptuple [] | PPpvar _ }, _ as p] -> p
  | l ->
      let i = { id = "(null)"; id_loc = loc; id_lab = [] } in
      let p = { pat_desc = Ptree.PPpvar i; pat_loc = loc } in
      let v = { pp_desc = Ptree.PPvar (Qident i); pp_loc = loc } in
      p, { pp_desc = PPmatch (v,l); pp_loc = loc }

let dpost ql = List.map (fun (loc, ql) -> mk_dpost loc ql) ql

let dxpost uc ql =
  let add_exn (q,pat,f) m =
    let xs = find_xsymbol uc q in
    Mexn.change (function
      | Some l -> Some ((pat,f) :: l)
      | None   -> Some ((pat,f) :: [])) xs m in
  let exn_map (loc,ql) =
    let m = List.fold_right add_exn ql Mexn.empty in
    Mexn.map (fun ql -> [mk_dpost loc ql]) m in
  let add_map ql m =
    Mexn.union (fun _ l r -> Some (l @ r)) (exn_map ql) m in
  List.fold_right add_map ql Mexn.empty

let dvariant uc var =
  List.map (fun (le,q) -> le, Opt.map (find_variant_ls uc) q) var

let dspec uc sp = {
  ds_pre     = sp.sp_pre;
  ds_post    = dpost sp.sp_post;
  ds_xpost   = dxpost uc sp.sp_xpost;
  ds_reads   = sp.sp_reads;
  ds_writes  = sp.sp_writes;
  ds_variant = dvariant uc sp.sp_variant;
}

let rec dtype_c denv (tyv, sp) =
  let tyv, dvty = dtype_v denv tyv in
  (tyv, dspec denv.uc sp), dvty

and dtype_v denv = function
  | Tpure pty ->
      let dity = dity_of_pty denv pty in
      DSpecV (false,dity), ([],dity)
  | Tarrow (bl,tyc) ->
      let denv,bl,tyl = dbinders denv bl in
      let tyc,(argl,res) = dtype_c denv tyc in
      DSpecA (bl,tyc), (tyl @ argl,res)

(* expressions *)

let de_unit ~loc = hidden_ls ~loc Mlw_expr.fs_void

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
  let loc = Opt.get_def loc uloc in
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
  | Ptree.Eletrec (fdl, e1) ->
      let fdl = dletrec denv fdl in
      let add_one denv ({ id = id }, _, dvty, _, _) =
        { denv with locals = Mstr.add id (denv.tvars, dvty) denv.locals } in
      let denv = List.fold_left add_one denv fdl in
      let e1 = dexpr denv e1 in
      DEletrec (fdl, e1), e1.de_type
  | Ptree.Efun (bl, tr) ->
      let denv, bl, tyl = dbinders denv bl in
      let tr, (argl, res) = dtriple denv tr in
      DEfun (bl, tr), (tyl @ argl, res)
  | Ptree.Ecast (e1, pty) ->
      let e1 = dexpr denv e1 in
      expected_type e1 (dity_of_pty denv pty);
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
  | Ptree.Econstant (Number.ConstInt _ as c) ->
      DEconstant c, ([], dity_int)
  | Ptree.Econstant (Number.ConstReal _ as c) ->
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
      let branch (q, pp, e) =
        let xs = find_xsymbol denv.uc q in
        let ety = specialize_xsymbol xs in
        let ppat, dity, denv = dpattern denv pp in
        unify_loc unify pp.pat_loc ety dity;
        let e = dexpr denv e in
        expected_type e res;
        xs, ppat, e in
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
  | Ptree.Eabstract (e1, sp) ->
      let e1 = dexpr denv e1 in
      let sp = dspec denv.uc sp in
      DEabstract (e1, sp), e1.de_type
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

and dletrec denv fdl =
  (* add all functions into the environment *)
  let add_one denv (_,id,_,bl,_) =
    let argl = List.map (fun _ -> create_type_variable ()) bl in
    let dvty = argl, create_type_variable () in
    let tvars = add_dvty denv.tvars dvty in
    let locals = Mstr.add id.id (tvars, dvty) denv.locals in
    { denv with locals = locals; tvars = tvars }, dvty in
  let denv, dvtyl = Lists.map_fold_left add_one denv fdl in
  (* then unify the binders *)
  let bind_one (_,_,_,bl,_) (argl,res) =
    let denv,bl,tyl = dbinders denv bl in
    List.iter2 unify argl tyl;
    denv,bl,tyl,res in
  let denvl = List.map2 bind_one fdl dvtyl in
  (* then type-check the bodies *)
  let type_one (loc,id,gh,_,tr) (denv,bl,tyl,tyv) =
    let tr, (argl, res) = dtriple denv tr in
    if argl <> [] then errorm ~loc
      "The body of a recursive function must be a first-order value";
    unify_loc unify loc tyv res;
    id, gh, (tyl, tyv), bl, tr in
  List.map2 type_one fdl denvl

and dtriple denv (e, sp) =
  let e = dexpr denv e in
  let sp = dspec denv.uc sp in
  (e, sp), e.de_type

(** stage 2 *)

type lenv = {
  mod_uc   : module_uc;
  th_at    : Theory.theory_uc;
  th_old   : Theory.theory_uc;
  let_vars : let_sym Mstr.t;
  log_vars : vsymbol Mstr.t;
}

let create_lenv uc = {
  mod_uc   = uc;
  th_at    = Theory.use_export (get_theory uc) Mlw_wp.th_mark_at;
  th_old   = Theory.use_export (get_theory uc) Mlw_wp.th_mark_old;
  let_vars = Mstr.empty;
  log_vars = Mstr.empty;
}

(* invariant handling *)

let env_invariant lenv eff pvs =
  let kn = get_known lenv.mod_uc in
  let lkn = Theory.get_known (get_theory lenv.mod_uc) in
  let regs = Sreg.union eff.eff_writes eff.eff_ghostw in
  let add_pv pv (pinv,qinv) =
    let ity = pv.pv_vtv.vtv_ity in
    let written r = reg_occurs r ity.ity_vars in
    let inv = Mlw_wp.full_invariant lkn kn pv.pv_vs ity in
    let qinv = (* we reprove invariants for modified non-reset variables *)
      if Sreg.exists written regs && not (eff_stale_region eff ity.ity_vars)
      then t_and_simp qinv inv else qinv in
    t_and_simp pinv inv, qinv
  in
  Spv.fold add_pv pvs (t_true,t_true)

let rec check_reset rvs t = match t.t_node with
  | Tvar vs when Svs.mem vs rvs ->
      errorm "The variable %s is reset and can only be used \
        under `old' in the postcondition" vs.vs_name.id_string
  | Tapp (ls,_) when ls_equal ls fs_at -> false
  | Tlet _ | Tcase _ | Teps _ | Tquant _ ->
      let rvs = Mvs.set_inter rvs t.t_vars in
      if Mvs.is_empty rvs then false else
      t_any (check_reset rvs) t
  | _ ->
      t_any (check_reset rvs) t

let post_invariant lenv rvs inv ity q =
  ignore (check_reset rvs q);
  let vs, q = open_post q in
  let kn = get_known lenv.mod_uc in
  let lkn = Theory.get_known (get_theory lenv.mod_uc) in
  let res_inv = Mlw_wp.full_invariant lkn kn vs ity in
  let q = t_and_asym_simp (t_and_simp res_inv inv) q in
  Mlw_ty.create_post vs q

let ity_or_unit = function
  | VTvalue v -> v.vtv_ity
  | VTarrow _ -> ity_unit

let reset_vars eff pvs =
  let add pv s =
    if eff_stale_region eff pv.pv_vtv.vtv_ity.ity_vars
    then Svs.add pv.pv_vs s else s in
  if Mreg.is_empty eff.eff_resets then Svs.empty else
  Spv.fold add pvs Svs.empty

(* add dummy postconditions for uncovered exceptions *)
let complete_xpost eff xq =
  let xe = Sexn.union eff.eff_raises eff.eff_ghostx in
  let check xs _ = Loc.errorm
    "this expression does not raise exception %a" print_xs xs in
  Mexn.iter check (Mexn.set_diff xq xe);
  let dummy { xs_ity = ity } () =
    let v = create_vsymbol (id_fresh "dummy") (ty_of_ity ity) in
    Mlw_ty.create_post v t_true in
  Mexn.set_union xq (Mexn.mapi dummy (Mexn.set_diff xe xq))

let spec_invariant lenv pvs vty spec =
  let ity = ity_or_unit vty in
  let pvs = spec_pvset pvs spec in
  let rvs = reset_vars spec.c_effect pvs in
  let xpost = complete_xpost spec.c_effect spec.c_xpost in
  let pinv,qinv = env_invariant lenv spec.c_effect pvs in
  let post_inv = post_invariant lenv rvs qinv in
  let xpost_inv xs q = post_inv xs.xs_ity q in
  { spec with c_pre   = t_and_asym_simp pinv spec.c_pre;
              c_post  = post_inv ity spec.c_post;
              c_xpost = Mexn.mapi xpost_inv xpost }

let abstr_invariant lenv e spec0 =
  let pvs = e_pvset Spv.empty e in
  let spec = { spec0 with c_effect = e.e_effect } in
  let spec = spec_invariant lenv pvs e.e_vty spec in
  (* we do not require invariants on free variables *)
  { spec with c_pre = spec0.c_pre }

let lambda_invariant lenv pvs eff lam =
  let pvs = List.fold_right Spv.add lam.l_args pvs in
  let spec = { lam.l_spec with c_effect = eff } in
  let spec = spec_invariant lenv pvs lam.l_expr.e_vty spec in
  { lam with l_spec = spec }

(* specification handling *)

let create_variant lenv (t,r) =
  let t = Typing.type_term lenv.th_at (find_vs lenv.mod_uc lenv.log_vars) t in
  count_term_tuples t;
  check_at t;
  t, r

let create_assert lenv f =
  let f = Typing.type_fmla lenv.th_at (find_vs lenv.mod_uc lenv.log_vars) f in
  let f = t_label_add Split_goal.stop_split f in
  count_term_tuples f;
  check_at f;
  f

let create_pre lenv fs = t_and_simp_l (List.map (create_assert lenv) fs)

let create_post lenv res pat f =
  let log_vars = match pat.pat_desc with
    | Ptree.PPpvar { id = x } ->
        Mstr.add x res lenv.log_vars
    | Ptree.PPptuple [] ->
        Loc.try2 pat.pat_loc Ty.ty_equal_check res.vs_ty ty_unit;
        lenv.log_vars
    | Ptree.PPpwild ->
        lenv.log_vars
    | _ -> assert false in
  let f = Typing.type_fmla lenv.th_old (find_vs lenv.mod_uc log_vars) f in
  let f = t_label_add Split_goal.stop_split f in
  let f = remove_old f in
  count_term_tuples f;
  check_at f;
  f

let create_post lenv ty fs =
  let rec get_name = function
    | ({ pat_desc = Ptree.PPpvar { id = "(null)" }},_)::l -> get_name l
    | ({ pat_desc = Ptree.PPpvar { id = x        }},_)::_ -> x
    | _::l -> get_name l
    | [] -> "result" in
  let res = create_vsymbol (id_fresh (get_name fs)) ty in
  let post (pat,f) = create_post lenv res pat f in
  let f = t_and_simp_l (List.map post fs) in
  Mlw_ty.create_post res f

let create_xpost lenv xs fs = create_post lenv (ty_of_ity xs.xs_ity) fs

let create_post lenv vty fs = create_post lenv (ty_of_vty vty) fs

let create_xpost lenv xq = Mexn.mapi (create_xpost lenv) xq

let add_local x lv lenv = match lv with
  | LetA _ ->
      { lenv with let_vars = Mstr.add x lv lenv.let_vars }
  | LetV pv ->
      { lenv with
        let_vars = Mstr.add x lv lenv.let_vars;
        log_vars = Mstr.add x pv.pv_vs lenv.log_vars }

let binders bl =
  let binder (id, ghost, dity) =
    let vtv = vty_value ~ghost (ity_of_dity dity) in
    create_pvsymbol (Denv.create_user_id id) vtv in
  List.map binder bl

let add_binders lenv pvl =
  let add lenv pv = add_local pv.pv_vs.vs_name.id_string (LetV pv) lenv in
  List.fold_left add lenv pvl

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
      let mut = Opt.map (reg_full_inst sbs) vtvv.vtv_mut in
      let ghost = vtv.vtv_ghost || vtvv.vtv_ghost in
      vs, vty_value ~ghost ?mut (ity_full_inst sbs vtvv.vtv_ity)
  | Ptree.PPcast (e,_) | Ptree.PPnamed (_,e) ->
      get_eff_expr lenv e
  | _ ->
      errorm ~loc "unsupported effect expression"

let get_eff_regs lenv fn (eff,svs) le =
  let vs, vtv = get_eff_expr lenv le in
  match vtv.vtv_mut, vtv.vtv_ity.ity_node with
  | Some reg, _ ->
      fn eff ?ghost:(Some vtv.vtv_ghost) reg, Svs.add vs svs
  | None, Ityapp (its,_,(_::_ as regl)) ->
      let csl = find_constructors (get_known lenv.mod_uc) its in
      let add_arg ((ngr,ghr) as regs) vtv = match vtv.vtv_mut with
        | Some r when vtv.vtv_ghost -> ngr, Sreg.add r ghr
        | Some r                    -> Sreg.add r ngr, ghr
        | None -> regs in
      let add_cs regs (cs,_) = List.fold_left add_arg regs cs.pl_args in
      let ngr, ghr = List.fold_left add_cs (Sreg.empty,Sreg.empty) csl in
      let add_reg eff reg0 reg =
        let eff = if not (Sreg.mem reg0 ngr) then eff else
          fn eff ?ghost:(Some vtv.vtv_ghost) reg in
        let eff = if not (Sreg.mem reg0 ghr) then eff else
          fn eff ?ghost:(Some true) reg in
        eff in
      List.fold_left2 add_reg eff its.its_regs regl, Svs.add vs svs
  | _ ->
      errorm ~loc:le.pp_loc "mutable expression expected"

let eff_of_deff lenv dsp =
  let acc = eff_empty, Svs.empty in
  let add_read acc e = get_eff_regs lenv eff_read acc e in
  let acc = List.fold_left add_read acc dsp.ds_reads in
  let add_write acc e = get_eff_regs lenv eff_write acc e in
  let eff, svs = List.fold_left add_write acc dsp.ds_writes in
  let add_raise xs _ eff = eff_raise eff xs in
  Mexn.fold add_raise dsp.ds_xpost eff, svs

let check_user_effect lenv e dsp =
  let acc = eff_empty, Svs.empty in
  let read le eff ?(ghost=false) reg =
    ignore ghost;
    if Sreg.mem reg e.e_effect.eff_reads ||
       Sreg.mem reg e.e_effect.eff_ghostr
    then eff else Loc.errorm ~loc:le.pp_loc
      "this read effect never happens in the expression" in
  let check_read e = ignore (get_eff_regs lenv (read e) acc e) in
  List.iter check_read dsp.ds_reads;
  let write le eff ?(ghost=false) reg =
    ignore ghost;
    if Sreg.mem reg e.e_effect.eff_writes ||
       Sreg.mem reg e.e_effect.eff_ghostw
    then eff else Loc.errorm ~loc:le.pp_loc
      "this write effect never happens in the expression" in
  let check_write e = ignore (get_eff_regs lenv (write e) acc e) in
  List.iter check_write dsp.ds_writes;
  let check_raise xs _ =
    if Sexn.mem xs e.e_effect.eff_raises ||
       Sexn.mem xs e.e_effect.eff_ghostx
    then () else Loc.errorm
      "this expression does not raise exception %a" print_xs xs in
  Mexn.iter check_raise dsp.ds_xpost

let spec_of_dspec lenv eff vty dsp = {
  c_pre     = create_pre lenv dsp.ds_pre;
  c_post    = create_post lenv vty dsp.ds_post;
  c_xpost   = create_xpost lenv dsp.ds_xpost;
  c_effect  = eff;
  c_variant = List.map (create_variant lenv) dsp.ds_variant;
  c_letrec  = 0;
}

let rec type_c lenv gh pvs vars (dtyv, dsp) =
  let vty = type_v lenv gh pvs vars dtyv in
  let eff, esvs = eff_of_deff lenv dsp in
  (* reset every new region in the result *)
  let eff = match vty with
    | VTvalue v ->
        let on_reg r e = if reg_occurs r vars then e else eff_reset e r in
        reg_fold on_reg v.vtv_ity.ity_vars eff
    | VTarrow _ -> eff in
  (* refresh every unmodified subregion of a modified region *)
  let writes = Sreg.union eff.eff_writes eff.eff_ghostw in
  let check u eff =
    let on_reg r e = if Sreg.mem r writes then e else eff_refresh e r u in
    reg_fold on_reg u.reg_ity.ity_vars eff in
  let eff = Sreg.fold check writes eff in
  let spec = spec_of_dspec lenv eff vty dsp in
  if spec.c_variant <> [] then Loc.errorm
    "variants are not allowed in a parameter declaration";
  (* we add a fake variant term for every external variable in effect
     expressions which also does not occur in pre/post/xpost. In this
     way, we store the variable in the specification in order to keep
     the effect from being erased by Mlw_ty.spec_filter. Variants are
     ignored outside of "let rec" definitions, so WP are not affected. *)
  let del_pv pv s = Svs.remove pv.pv_vs s in
  let esvs = Spv.fold del_pv pvs esvs in
  let drop _ t s = Mvs.set_diff s t.t_vars in
  let esvs = drop () spec.c_pre esvs in
  let esvs = drop () spec.c_post esvs in
  let esvs = Mexn.fold drop spec.c_xpost esvs in
  let add_vs vs varl = (t_var vs, None) :: varl in
  let varl = Svs.fold add_vs esvs spec.c_variant in
  let spec = { spec with c_variant = varl } in
  (* add the invariants *)
  spec_invariant lenv pvs vty spec, vty

and type_v lenv gh pvs vars = function
  | DSpecV (ghost,v) ->
      let ghost = ghost || gh in
      VTvalue (vty_value ~ghost (ity_of_dity v))
  | DSpecA (bl,tyc) ->
      let pvl = binders bl in
      let lenv = add_binders lenv pvl in
      let add_pv pv s = vars_union pv.pv_vars s in
      let vars = List.fold_right add_pv pvl vars in
      let pvs = List.fold_right Spv.add pvl pvs in
      let spec, vty = type_c lenv gh pvs vars tyc in
      VTarrow (vty_arrow pvl ~spec vty)

(* expressions *)

(* dead code
let vty_ghostify gh vty =
  if gh && not (vty_ghost vty) then vty_ghostify vty else vty
*)

let e_ghostify gh e =
  if gh && not (vty_ghost e.e_vty) then e_ghost e else e

let e_app_gh e el =
  let rec decomp = function
    | VTvalue _ -> []
    | VTarrow a -> a.vta_args @ decomp a.vta_result in
  let rec ghostify = function
    | _, [] -> []
    | [], _ -> assert false
    | pv :: pvl, e :: el ->
        e_ghostify pv.pv_vtv.vtv_ghost e :: ghostify (pvl, el)
  in
  e_app e (ghostify (decomp e.e_vty, el))

let e_plapp_gh pl el ity =
  let ghostify vtv e = e_ghostify vtv.vtv_ghost e in
  e_plapp pl (List.map2 ghostify pl.pl_args el) ity

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
  | DElet (x, gh, { de_desc = DEfun (bl, tr) }, de2) ->
      let fd = expr_fun lenv x gh bl tr in
      let lenv = add_local x.id (LetA fd.fun_ps) lenv in
      let e2 = expr lenv de2 in
      e_rec [fd] e2
  | DEfun (bl, tr) ->
      let x = mk_id "fn" loc in
      let fd = expr_fun lenv x false bl tr in
      let e2 = e_arrow fd.fun_ps fd.fun_ps.ps_vta in
      e_rec [fd] e2
  (* FIXME? (ghost "lab" fun x -> ...) loses the label "lab" *)
  | DEghost { de_desc = DEfun (bl, tr) } ->
      let x = mk_id "fn" loc in
      let fd = expr_fun lenv x true bl tr in
      let e2 = e_arrow fd.fun_ps fd.fun_ps.ps_vta in
      e_rec [fd] e2
  | DElet (x, gh, de1, de2) ->
      let e1 = e_ghostify gh (expr lenv de1) in
      let mk_expr e1 =
        let def1 = create_let_defn (Denv.create_user_id x) e1 in
        let name = match def1.let_sym with
          | LetA ps -> ps.ps_name | LetV pv -> pv.pv_vs.vs_name in
        let lenv = add_local x.id def1.let_sym lenv in
        let e2 = expr lenv de2 in
        let ghost_unit = match e2.e_vty with
          | VTvalue { vtv_ghost = true; vtv_mut = None; vtv_ity = ity } ->
              ity_equal ity ity_unit
          | _ -> false in
        let e2 =
          if ghost_unit (* e2 is immutable ghost unit *)
             && not (vty_ghost e1.e_vty) (* and e1 is non-ghost *)
             && not (Mid.mem name e2.e_varm) (* and x doesn't occur in e2 *)
          then e_let (create_let_defn (id_fresh "gh") e2) e_void else e2 in
        e_let def1 e2 in
      let rec flatten e1 = match e1.e_node with
        | Elet (ld,_) (* can't let a non-ghost expr from a ghost one *)
          when gh && not (vty_ghost ld.let_expr.e_vty) -> mk_expr e1
        | Elet (ld,e1) -> e_let ld (flatten e1)
        | _ -> mk_expr e1 in
      begin match e1.e_vty with
        | VTarrow { vta_ghost = true } when not gh ->
            errorm ~loc "%s must be a ghost function" x.id
        | VTarrow _ -> flatten e1
        | VTvalue _ -> mk_expr e1
      end;
  | DEletrec (fdl, de1) ->
      let fdl = expr_rec lenv fdl in
      let add_fd { fun_ps = ps } = add_local ps.ps_name.id_string (LetA ps) in
      let e1 = expr (List.fold_right add_fd fdl lenv) de1 in
      e_rec fdl e1
  | DEapply (de1, del) ->
      let el = List.map (expr lenv) del in
      begin match de1.de_desc with
        | DEglobal_pl pls -> e_plapp_gh pls el (ity_of_dity (snd de.de_type))
        | DEglobal_ls ls  -> e_lapp ls el (ity_of_dity (snd de.de_type))
        | _               -> e_app_gh (expr lenv de1) el
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
  | DEabstract (de1, dsp) ->
      let e1 = expr lenv de1 in
      let spec = spec_of_dspec lenv e1.e_effect e1.e_vty dsp in
      if spec.c_variant <> [] then Loc.errorm
        "variants are not allowed in `abstract'";
      check_user_effect lenv e1 dsp;
      let spec = abstr_invariant lenv e1 spec in
      e_abstract e1 spec
  | DEassert (ak, f) ->
      let ak = match ak with
        | Ptree.Aassert -> Aassert
        | Ptree.Aassume -> Aassume
        | Ptree.Acheck  -> Acheck in
      e_assert ak (create_assert lenv f)
  | DEabsurd ->
      e_absurd (ity_of_dity (snd de.de_type))
  | DEraise (xs, de1) ->
      e_raise xs (expr lenv de1) (ity_of_dity (snd de.de_type))
  | DEtry (de1, bl) ->
      let e1 = expr lenv de1 in
      let add_branch (m,l) (xs,pp,de) =
        let vm, pp = make_ppattern pp (vty_value xs.xs_ity) in
        let lenv = Mstr.fold (fun s pv -> add_local s (LetV pv)) vm lenv in
        let e = expr lenv de in
        try Mexn.add xs ((pp,e) :: Mexn.find xs m) m, l
        with Not_found -> Mexn.add xs [pp,e] m, (xs::l) in
      let xsm, xsl = List.fold_left add_branch (Mexn.empty,[]) bl in
      let mk_branch xs = match Mexn.find xs xsm with
        | [{ ppat_pattern = { pat_node = Pvar vs }}, e] ->
            xs, Mlw_ty.restore_pv vs, e
        | [{ ppat_pattern = { pat_node = Pwild }} as p, e] ->
            xs, create_pvsymbol (id_fresh "wild") p.ppat_vtv, e
        | [{ ppat_pattern = { pat_node = Papp (fs,[]) }} as p, e]
          when ls_equal fs Mlw_expr.fs_void ->
            xs, create_pvsymbol (id_fresh "void") p.ppat_vtv, e
        | bl ->
            let pv = create_pvsymbol (id_fresh "res") (vty_value xs.xs_ity) in
            let pl = List.rev_map (fun (p,_) -> [p.ppat_pattern],t_void) bl in
            let lkn = Theory.get_known (get_theory lenv.mod_uc) in
            let find ts = List.map fst (Decl.find_constructors lkn ts) in
            let bl = try
              ignore (Pattern.CompileTerm.compile find [t_var pv.pv_vs] pl);
              bl
            with Pattern.NonExhaustive _ ->
              let ity = ity_of_dity (snd de.de_type) in
              let _, pp = make_ppattern PPwild pv.pv_vtv in
              (pp, e_raise xs (e_value pv) ity) :: bl
            in
            xs, pv, e_case (e_value pv) (List.rev bl)
      in
      e_try e1 (List.rev_map mk_branch xsl)
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
      let spec, result = type_c lenv false Spv.empty vars_empty dtyc in
      e_any spec result
  | DEghost de1 ->
      e_ghostify true (expr lenv de1)
  | DEloop (var,inv,de1) ->
      let inv = create_pre lenv inv in
      let var = List.map (create_variant lenv) var in
      e_loop inv var (expr lenv de1)
  | DEfor (x,defrom,dir,deto,inv,de1) ->
      let efrom = expr lenv defrom in
      let eto = expr lenv deto in
      let pv = create_pvsymbol (Denv.create_user_id x) (vty_value ity_int) in
      let lenv = add_local x.id (LetV pv) lenv in
      let inv = create_pre lenv inv in
      let e1 = expr lenv de1 in
      let dir = match dir with
        | Ptree.To -> To
        | Ptree.Downto -> DownTo in
      e_for pv efrom dir eto inv e1

and expr_rec lenv dfdl =
  let step1 lenv (id, gh, _, bl, ((de, _) as tr)) =
    let pvl = binders bl in
    let vta = vty_arrow pvl ~ghost:gh (vty_of_dvty de.de_type) in
    let ps = create_psymbol (Denv.create_user_id id) vta in
    add_local id.id (LetA ps) lenv, (ps, gh, pvl, tr) in
  let lenv, fdl = Lists.map_fold_left step1 lenv dfdl in
  let step2 (ps, gh, pvl, tr) = ps, expr_lam lenv gh pvl tr in
  let fdl = List.map step2 fdl in
  let rd_pvset pvs (_, lam) = l_pvset pvs lam in
  let pvs = List.fold_left rd_pvset Spv.empty fdl in
  let rd_effect eff (_, lam) = eff_union eff lam.l_expr.e_effect in
  let eff = List.fold_left rd_effect eff_empty fdl in
  let step3 (ps, lam) = ps, lambda_invariant lenv pvs eff lam in
  let fdl = create_rec_defn (List.map step3 fdl) in
  let check_user_effect { fun_lambda = l } (_,_,_,_,(de,dsp)) =
    Loc.try3 de.de_loc check_user_effect lenv l.l_expr dsp in
  List.iter2 check_user_effect fdl dfdl;
  fdl

and expr_fun lenv x gh bl (_, dsp as tr) =
  let lam = expr_lam lenv gh (binders bl) tr in
  if lam.l_spec.c_variant <> [] then Loc.errorm
    "variants are not allowed in a non-recursive definition";
  check_user_effect lenv lam.l_expr dsp;
  let lam =
    if Debug.nottest_flag implicit_post || dsp.ds_post <> [] ||
       oty_equal lam.l_spec.c_post.t_ty (Some ty_unit) then lam
    else match e_purify lam.l_expr with
    | None -> lam
    | Some t ->
        let vs, f = Mlw_ty.open_post lam.l_spec.c_post in
        let f = t_and_simp (t_equ_simp (t_var vs) t) f in
        let f = t_label_add Split_goal.stop_split f in
        let post = Mlw_ty.create_post vs f in
        let spec = { lam.l_spec with c_post = post } in
        { lam with l_spec = spec } in
  let pvs = l_pvset Spv.empty lam in
  let lam = lambda_invariant lenv pvs lam.l_expr.e_effect lam in
  create_fun_defn (Denv.create_user_id x) lam

and expr_lam lenv gh pvl (de, dsp) =
  let lenv = add_binders lenv pvl in
  let e = e_ghostify gh (expr lenv de) in
  if not gh && vty_ghost e.e_vty then
    errorm ~loc:de.de_loc "ghost body in a non-ghost function";
  let spec = spec_of_dspec lenv e.e_effect e.e_vty dsp in
  { l_args = pvl; l_expr = e; l_spec = spec }

(** Type declaration *)

let add_type_invariant loc uc id params inv =
  let x = "self" in
  let its = match uc_find_ts uc (Qident id) with
    | PT its when its.its_inv -> its
    | _ -> errorm ~loc "type %s does not have an invariant" id.id in
  let add_tv acc { id = id; id_loc = loc } =
    let e = Loc.Located (loc, DuplicateTypeVar id) in
    Sstr.add_new e id acc, Typing.create_user_tv id in
  let _, tvl = Lists.map_fold_left add_tv Sstr.empty params in
  let ty = ty_app its.its_pure (List.map ty_var tvl) in
  let res = create_vsymbol (id_fresh x) ty in
  let find = function
    | Qident { id = id } when id = x -> Some res
    | _ -> None in
  let mk_inv f =
    let f = Typing.type_fmla (get_theory uc) find f in
    t_label_add Split_goal.stop_split f in
  let inv = List.map mk_inv inv in
  let q = Mlw_ty.create_post res (t_and_simp_l inv) in
  let q = if List.for_all2 tv_equal its.its_args tvl then q else
    let add mtv u v = Mtv.add u (ty_var v) mtv in
    let mtv = List.fold_left2 add Mtv.empty tvl its.its_args in
    t_ty_subst mtv Mvs.empty q in
  let uc = (count_term_tuples q; flush_tuples uc) in
  Mlw_module.add_invariant uc its q

let look_for_loc tdl s =
  let look_id loc id = if id.id = s then Some id.id_loc else loc in
  let look_pj loc (id,_) = Opt.fold look_id loc id in
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

let add_types ~wp uc tdl =
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

  (* detect mutable types and invariants *)

  let mutables = Hstr.create 5 in
  let rec mut_visit x =
    try Hstr.find mutables x
    with Not_found ->
      let ts_mut = function
        | Qident { id = x } when Mstr.mem x def -> mut_visit x
        | q ->
            begin match uc_find_ts uc q with
              | PT its -> its.its_regs <> [] || its.its_inv
              | TS _ -> false
            end
      in
      let rec check = function
        | PPTtyvar _ -> false
        | PPTtyapp (tyl,q) -> ts_mut q || List.exists check tyl
        | PPTtuple tyl -> List.exists check tyl in
      Hstr.replace mutables x false;
      let mut =
        let td = Mstr.find x def in
        td.td_inv <> [] ||
        match td.td_def with
        | TDabstract -> false
        | TDalias ty -> check ty
        | TDalgebraic csl ->
            let proj (_,pty) = check pty in
            List.exists (fun (_,_,l) -> List.exists proj l) csl
        | TDrecord fl ->
            let field f = f.f_mutable || check f.f_pty in
            List.exists field fl in
      Hstr.replace mutables x mut;
      mut
  in
  Mstr.iter (fun x _ -> ignore (mut_visit x)) def;

  (* create type symbols and predefinitions for mutable types *)

  let tysymbols = Hstr.create 5 in
  let predefs = Hstr.create 5 in
  let rec its_visit x =
    try match Hstr.find tysymbols x with
      | Some ts -> ts
      | None ->
          let td = Mstr.find x def in let loc = td.td_loc in
          if td.td_inv <> []
          then errorm ~loc "Recursive types cannot have invariants"
          else errorm ~loc "Recursive types cannot have mutable components"
    with Not_found ->
      let d = Mstr.find x def in
      let add_tv acc id =
        let e = Loc.Located (id.id_loc, DuplicateTypeVar id.id) in
        let tv = Typing.create_user_tv id.id in
        Mstr.add_new e id.id tv acc in
      let vars = List.fold_left add_tv Mstr.empty d.td_params in
      let vl = List.map (fun id -> Mstr.find id.id vars) d.td_params in
      let id = Denv.create_user_id d.td_ident in
      let abst = d.td_vis = Abstract in
      let priv = d.td_vis = Private in
      Hstr.add tysymbols x None;
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
            create_itysymbol id ~abst ~priv ~inv:false vl rl (Some def)
        | TDalgebraic csl when Hstr.find mutables x ->
            let projs = Hstr.create 5 in
            (* to check projections' types we must fix the tyvars *)
            let add s v = let t = ity_var v in ity_match s t t in
            let sbs = List.fold_left add ity_subst_empty vl in
            let mk_proj (regs,inv) (id,pty) =
              let ity = parse pty in
              let vtv = vty_value ity in
              let inv = inv || ity_has_inv ity in
              match id with
                | None ->
                    let pv = create_pvsymbol (id_fresh "pj") vtv in
                    (Sreg.union regs ity.ity_vars.vars_reg, inv), (pv, false)
                | Some id ->
                    try
                      let pv = Hstr.find projs id.id in
                      let ty = pv.pv_vtv.vtv_ity in
                      (* TODO: once we have ghost/mutable fields in algebraics,
                         don't forget to check here that they coincide, too *)
                      ignore (Loc.try3 id.id_loc ity_match sbs ty ity);
                      (regs, inv), (pv, true)
                    with Not_found ->
                      let pv = create_pvsymbol (Denv.create_user_id id) vtv in
                      Hstr.replace projs id.id pv;
                      (Sreg.union regs ity.ity_vars.vars_reg, inv), (pv, true)
            in
            let mk_constr s (_loc,cid,pjl) =
              let s,pjl = Lists.map_fold_left mk_proj s pjl in
              s, (Denv.create_user_id cid, pjl)
            in
            let init = (Sreg.empty, d.td_inv <> []) in
            let (regs,inv),def = Lists.map_fold_left mk_constr init csl in
            Hstr.replace predefs x def;
            create_itysymbol id ~abst ~priv ~inv vl (Sreg.elements regs) None
        | TDrecord fl when Hstr.find mutables x ->
            let mk_field (regs,inv) f =
              let ghost = f.f_ghost in
              let ity = parse f.f_pty in
              let inv = inv || ity_has_inv ity in
              let fid = Denv.create_user_id f.f_ident in
              let regs,mut = if f.f_mutable then
                let r = create_region fid ity in
                Sreg.add r regs, Some r
              else
                Sreg.union regs ity.ity_vars.vars_reg, None
              in
              let vtv = vty_value ?mut ~ghost ity in
              (regs, inv), (create_pvsymbol fid vtv, true)
            in
            let init = (Sreg.empty, d.td_inv <> []) in
            let (regs,inv),pjl = Lists.map_fold_left mk_field init fl in
            let cid = { d.td_ident with id = "mk " ^ d.td_ident.id } in
            Hstr.replace predefs x [Denv.create_user_id cid, pjl];
            create_itysymbol id ~abst ~priv ~inv vl (Sreg.elements regs) None
        | TDalgebraic _ | TDrecord _ | TDabstract ->
            create_itysymbol id ~abst ~priv ~inv:false vl [] None
      in
      Hstr.add tysymbols x (Some ts);
      ts
  in
  Mstr.iter (fun x _ -> ignore (its_visit x)) def;

  (* create predefinitions for immutable types *)

  let def_visit d (abstr,algeb,alias) =
    let x = d.td_ident.id in
    let ts = Opt.get (Hstr.find tysymbols x) in
    let add_tv s x v = Mstr.add x.id v s in
    let vars = List.fold_left2 add_tv Mstr.empty d.td_params ts.its_args in
    let get_ts = function
      | Qident { id = x } when Mstr.mem x def ->
          PT (Opt.get (Hstr.find tysymbols x))
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
      | (TDalgebraic _ | TDrecord _) when Hstr.find mutables x ->
          abstr, (ts, Hstr.find predefs x) :: algeb, alias
      | TDalgebraic csl ->
          let projs = Hstr.create 5 in
          let mk_proj (id,pty) =
            let ity = parse pty in
            let vtv = vty_value ity in
            match id with
              | None ->
                  create_pvsymbol (id_fresh "pj") vtv, false
              | Some id ->
                  try
                    let pv = Hstr.find projs id.id in
                    let ty = pv.pv_vtv.vtv_ity in
                    (* once we have ghost/mutable fields in algebraics,
                       don't forget to check here that they coincide, too *)
                    Loc.try2 id.id_loc ity_equal_check ty ity;
                    pv, true
                  with Not_found ->
                    let pv = create_pvsymbol (Denv.create_user_id id) vtv in
                    Hstr.replace projs id.id pv;
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
    ts.its_abst || ts.its_priv || ts.its_inv || ts.its_regs <> [] ||
    Opt.fold (fun _ -> check) false ts.its_def
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
      add_pdecl_with_tuples ~wp uc (create_ty_decl ts)
    else
      add_decl_with_tuples uc (Decl.create_ty_decl ts.its_pure)
  in
  let add_invariant uc d = if d.td_inv = [] then uc else
    add_type_invariant d.td_loc uc d.td_ident d.td_params d.td_inv
  in
  try
    let uc = List.fold_left add_type_decl uc abstr in
    let uc = if algeb = [] then uc else
      if List.exists is_impure_data algeb then
        add_pdecl_with_tuples ~wp uc (create_data_decl algeb)
      else
        let d = List.map mk_pure_decl algeb in
        add_decl_with_tuples uc (Decl.create_data_decl d)
    in
    let uc = List.fold_left add_type_decl uc alias in
    let uc = List.fold_left add_invariant uc tdl in
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

let add_types ~wp uc tdl = match tdl with
  (* a single abstract type with an invariant is a late invariant
     declaration which adds an invariant to a recently declared
     program type (which must already have an invariant, e.g. true).
     Otherwise, we trust the parser to not produce abstract or alias
     type declarations with invariants. *)
  | [{ td_def = TDabstract; td_inv = _::_  as inv} as d] ->
      add_type_invariant d.td_loc uc d.td_ident d.td_params inv
  | _ -> add_types ~wp uc tdl

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

(** Top level *)

let add_decl loc uc decl =
  let th0 = Mlw_module.get_theory uc in
  let dl0 = Theory.get_rev_decls th0 in
  let seen td = match dl0 with
    | td0 :: _ -> td_equal td td0
    | [] -> false in
  (* we extract the added declarations and readd it to uc *)
  let rec add_td uc = function
    | [] -> uc
    | td :: _ when seen td -> uc
    | { td_node = Theory.Decl d } :: dl ->
        Mlw_module.add_decl (add_td uc dl) d
    | { td_node = Theory.Meta (m,al) } :: dl ->
        Mlw_module.add_meta (add_td uc dl) m al
    | { td_node = Theory.Use th } :: dl ->
        Mlw_module.use_export_theory (add_td uc dl) th
    | { td_node = Theory.Clone _ } :: _ -> assert false
  in
  add_td uc (Theory.get_rev_decls (Typing.add_decl loc th0 decl))

let add_decl ~wp loc uc = function
  | TypeDecl tdl -> add_types ~wp uc tdl
  | decl -> add_decl loc uc decl

let add_decl ~wp loc uc d =
  if Debug.test_flag Typing.debug_parse_only then uc else
  Loc.try3 loc (add_decl ~wp) loc uc d

let add_pdecl ~wp loc uc = function
  | Dlet (id, gh, e) ->
      let e = dexpr (create_denv uc) e in
      let pd = match e.de_desc with
        | DEfun (bl, tr) ->
            let fd = expr_fun (create_lenv uc) id gh bl tr in
            create_rec_decl [fd]
        | _ ->
            let e = e_ghostify gh (expr (create_lenv uc) e) in
            if not gh && vty_ghost e.e_vty then
              errorm ~loc "%s must be a ghost variable" id.id;
            let def = create_let_defn (Denv.create_user_id id) e in
            create_let_decl def in
      add_pdecl_with_tuples ~wp uc pd
  | Dletrec fdl ->
      let fdl = dletrec (create_denv uc) fdl in
      let fdl = expr_rec (create_lenv uc) fdl in
      let pd = create_rec_decl fdl in
      add_pdecl_with_tuples ~wp uc pd
  | Dexn (id, pty) ->
      let ity = ity_of_dity (dity_of_pty (create_denv uc) pty) in
      let xs = create_xsymbol (Denv.create_user_id id) ity in
      let pd = create_exn_decl xs in
      add_pdecl_with_tuples ~wp uc pd
  | Dparam (id, gh, tyv) ->
      let tyv, _ = dtype_v (create_denv uc) tyv in
      let tyv = type_v (create_lenv uc) gh Spv.empty vars_empty tyv in
      let lv = match tyv with
        | VTvalue v ->
            if v.vtv_ghost && not gh then
              errorm ~loc "%s must be a ghost variable" id.id;
            LetV (create_pvsymbol (Denv.create_user_id id) v)
        | VTarrow a ->
            if a.vta_ghost && not gh then
              errorm ~loc "%s must be a ghost function" id.id;
            LetA (create_psymbol (Denv.create_user_id id) a) in
      let pd = create_val_decl lv in
      add_pdecl_with_tuples ~wp uc pd

let add_pdecl ~wp loc uc d =
  if Debug.test_flag Typing.debug_parse_only then uc else
  Loc.try3 loc (add_pdecl ~wp) loc uc d

let use_clone_pure lib mth uc loc (use,inst) =
  let path, s = Typing.split_qualid use.use_theory in
  let th = find_theory loc lib mth path s in
  (* open namespace, if any *)
  let uc = if use.use_imp_exp = None then uc
  else Theory.open_namespace uc use.use_as in
  (* use or clone *)
  let uc = match inst with
    | None -> Theory.use_export uc th
    | Some inst -> Theory.clone_export uc th (Typing.type_inst uc th inst) in
  (* close namespace, if any *)
  match use.use_imp_exp with
    | None -> uc
    | Some imp -> Theory.close_namespace uc imp

let use_clone_pure lib mth uc loc use =
  if Debug.test_flag Typing.debug_parse_only then uc else
  Loc.try3 loc (use_clone_pure lib mth) uc loc use

let use_clone lib mmd mth uc loc (use,inst) =
  let path, s = Typing.split_qualid use.use_theory in
  let mth = find_module loc lib mmd mth path s in
  (* open namespace, if any *)
  let uc = if use.use_imp_exp = None then uc
  else open_namespace uc use.use_as in
  (* use or clone *)
  let uc = match mth, inst with
    | Module m, None -> use_export uc m
    | Theory th, None -> use_export_theory uc th
    | Module m, Some inst ->
        clone_export uc m (Typing.type_inst (get_theory uc) m.mod_theory inst)
    | Theory th, Some inst ->
        clone_export_theory uc th (Typing.type_inst (get_theory uc) th inst) in
  (* close namespace, if any *)
  match use.use_imp_exp with
    | None -> uc
    | Some imp -> close_namespace uc imp

let use_clone lib mmd mth uc loc use =
  if Debug.test_flag Typing.debug_parse_only then uc else
  Loc.try3 loc (use_clone lib mmd mth) uc loc use

let close_theory (mmd,mth) uc =
  if Debug.test_flag Typing.debug_parse_only then (mmd,mth) else
  let th = Theory.close_theory uc in
  let id = th.th_name.id_string in
  let loc = th.th_name.Ident.id_loc in
  if Mstr.mem id mmd then Loc.errorm ?loc "clash with previous module %s" id;
  if Mstr.mem id mth then Loc.errorm ?loc "clash with previous theory %s" id;
  mmd, Mstr.add id th mth

let close_module (mmd,mth) uc =
  if Debug.test_flag Typing.debug_parse_only then (mmd,mth) else
  let m = close_module uc in
  let id = m.mod_theory.th_name.id_string in
  let loc = m.mod_theory.th_name.Ident.id_loc in
  if Mstr.mem id mmd then Loc.errorm ?loc "clash with previous module %s" id;
  if Mstr.mem id mth then Loc.errorm ?loc "clash with previous theory %s" id;
  Mstr.add id m mmd, Mstr.add id m.mod_theory mth

let open_file, close_file =
  let inm  = Stack.create () in
  let tuc  = Stack.create () in
  let muc  = Stack.create () in
  let lenv = Stack.create () in
  let open_file lib path =
    let env = Env.env_of_library lib in
    let wp = path = [] && Debug.nottest_flag Typing.debug_type_only in
    Stack.push (Mstr.empty,Mstr.empty) lenv;
    let open_theory id = Stack.push false inm;
      Stack.push (Theory.create_theory ~path (Denv.create_user_id id)) tuc in
    let open_module id = Stack.push true inm;
      Stack.push (create_module env ~path (Denv.create_user_id id)) muc in
    let close_theory () = ignore (Stack.pop inm);
      Stack.push (close_theory (Stack.pop lenv) (Stack.pop tuc)) lenv in
    let close_module () = ignore (Stack.pop inm);
      Stack.push (close_module (Stack.pop lenv) (Stack.pop muc)) lenv in
    let open_namespace name = if Stack.top inm
      then Stack.push (Mlw_module.open_namespace (Stack.pop muc) name) muc
      else Stack.push (Theory.open_namespace (Stack.pop tuc) name) tuc in
    let close_namespace imp = if Stack.top inm
      then Stack.push (Mlw_module.close_namespace (Stack.pop muc) imp) muc
      else Stack.push (Theory.close_namespace (Stack.pop tuc) imp) tuc in
    let new_decl loc d = if Stack.top inm
      then Stack.push (add_decl ~wp loc (Stack.pop muc) d) muc
      else Stack.push (Typing.add_decl loc (Stack.pop tuc) d) tuc in
    let new_pdecl loc d =
      Stack.push (add_pdecl ~wp loc (Stack.pop muc) d) muc in
    let use_clone loc use = let (mmd,mth) = Stack.top lenv in if Stack.top inm
      then Stack.push (use_clone lib mmd mth (Stack.pop muc) loc use) muc
      else Stack.push (use_clone_pure lib mth (Stack.pop tuc) loc use) tuc in
    { open_theory = open_theory;
      close_theory = close_theory;
      open_module = open_module;
      close_module = close_module;
      open_namespace = open_namespace;
      close_namespace = (fun loc -> Loc.try1 loc close_namespace);
      new_decl = new_decl;
      new_pdecl = new_pdecl;
      use_clone = use_clone; }
  in
  let close_file () = Stack.pop lenv in
  open_file, close_file
