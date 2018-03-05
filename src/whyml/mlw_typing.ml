(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2018   --   Inria - CNRS - Paris-Sud University  *)
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
open Ptree

open Mlw_ty
open Mlw_ty.T
open Mlw_expr
open Mlw_decl
open Mlw_pretty
open Mlw_dexpr
open Mlw_module
open Mlw_wp

(** errors *)

exception DuplicateTypeVar of string
exception UnboundTypeVar of string

(** lazy declaration of tuples *)

let ht_tuple   = Hint.create 3
let ts_tuple n = Hint.replace ht_tuple n (); ts_tuple n
let fs_tuple n = Hint.replace ht_tuple n (); fs_tuple n

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

let add_pdecl_with_tuples ~wp uc pd =
  if Debug.test_flag Glob.flag then Sid.iter Glob.def pd.pd_news;
  add_pdecl ~wp (flush_tuples uc) pd

let add_decl_with_tuples uc d =
  if Debug.test_flag Glob.flag then Sid.iter Glob.def d.d_news;
  add_decl (flush_tuples uc) d

(** symbol lookup *)

let qloc = Typing.qloc
let print_qualid = Typing.print_qualid

let ns_find_ts ns p =
  let get_id_ts = function
    | PT pt -> pt.its_ts.ts_name
    | TS ts -> ts.ts_name in
  Typing.find_qualid get_id_ts ns_find_type_symbol ns p

let uc_find_ts uc p = ns_find_ts (get_namespace uc) p

let ns_find_ps ns p =
  let get_id_ps = function
    | PV pv -> pv.pv_vs.vs_name
    | PS ps -> ps.ps_name
    | PL pl -> pl.pl_ls.ls_name
    | XS xs -> xs.xs_name
    | LS ls -> ls.ls_name in
  Typing.find_qualid get_id_ps ns_find_prog_symbol ns p

let uc_find_ps uc p = ns_find_ps (get_namespace uc) p

let uc_find_ls uc p =
  let ns = Theory.get_namespace (get_theory uc) in
  Typing.find_qualid (fun ls -> ls.ls_name) Theory.ns_find_ls ns p

(** parsing types *)

let ity_of_pty ?(noop=true) uc pty =
  let rec get_ty = function
    | PTtyvar ({id_loc = loc}, true) when noop ->
        Loc.errorm ~loc "Opaqueness@ annotations@ are@ only@ \
          allowed@ in@ the@ types@ of@ formal@ arguments"
    | PTtyvar ({id_str = x}, _) ->
        ity_var (tv_of_string x)
    | PTtyapp (q, tyl) ->
        let tyl = List.map get_ty tyl in
        begin match uc_find_ts uc q with
        | PT s -> Loc.try2 ~loc:(qloc q) ity_app_fresh s tyl
        | TS s -> Loc.try2 ~loc:(qloc q) ity_pur s tyl
        end
    | PTtuple tyl ->
        let s = ts_tuple (List.length tyl) in
        ity_pur s (List.map get_ty tyl)
    | PTarrow (ty1, ty2) ->
        ity_pur ts_func [get_ty ty1; get_ty ty2]
    | PTparen ty ->
        get_ty ty
  in
  get_ty pty

let rec opaque_tvs acc = function
  | PTtyvar (id, true) -> Stv.add (tv_of_string id.id_str) acc
  | PTtyvar (_, false) -> acc
  | PTtyapp (_, pl)
  | PTtuple pl -> List.fold_left opaque_tvs acc pl
  | PTarrow (ty1, ty2) -> opaque_tvs (opaque_tvs acc ty1) ty2
  | PTparen ty -> opaque_tvs acc ty

(** typing program expressions *)

(* records *)

let parse_prog_record uc fll =
  let pl = match fll with
    | [] -> raise EmptyRecord
    | (pl,_)::_ -> pl in
  let its = match pl.pl_args with
    | [{ fd_ity = { ity_node = Ityapp (its,_,_) }}] -> its
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
  | _ -> Loc.errorm ~loc:(qloc p) "Not a record field: %a" print_qualid p

let find_pure_field uc (p,e) = match uc_find_ps uc p with LS ls -> ls, e
  | _ -> Loc.errorm ~loc:(qloc p) "Not a record field: %a" print_qualid p

let prog_record ~loc uc get_val fl =
  let fl = List.map (find_prog_field uc) fl in
  let cs,pjl,flm = Loc.try2 ~loc parse_prog_record uc fl in
  let get_val pj = get_val cs pj (Mls.find_opt pj.pl_ls flm) in
  cs, List.map get_val pjl

let pure_record ~loc uc get_val fl =
  let fl = List.map (find_pure_field uc) fl in
  let kn = Theory.get_known (get_theory uc) in
  let cs,pjl,flm = Loc.try2 ~loc Decl.parse_record kn fl in
  let get_val pj = get_val cs pj (Mls.find_opt pj flm) in
  cs, List.map get_val pjl

(* patterns *)

let create_user_id = Typing.create_user_id

let rec dpattern uc { pat_desc = desc; pat_loc = loc } =
  Mlw_dexpr.dpattern ~loc (match desc with
    | Ptree.Pwild -> DPwild
    | Ptree.Pvar x -> DPvar (create_user_id x)
    | Ptree.Papp (q,pl) ->
        begin match uc_find_ps uc q with
        | PL s -> DPpapp (s, List.map (fun p -> dpattern uc p) pl)
        | LS s -> DPlapp (s, List.map (fun p -> dpattern uc p) pl)
        | _ -> Loc.errorm ~loc:(qloc q) "Not a constructor: %a" print_qualid q
        end
    | Ptree.Prec [] -> raise Decl.EmptyRecord
    | Ptree.Prec ((q,_)::_ as fl) ->
        let get_val _ _ = function
          | Some p -> dpattern uc p
          | None -> Mlw_dexpr.dpattern DPwild in
        begin match uc_find_ps uc q with
        | PL _ -> let cs,fl = prog_record ~loc uc get_val fl in DPpapp (cs,fl)
        | LS _ -> let cs,fl = pure_record ~loc uc get_val fl in DPlapp (cs,fl)
        | _ -> Loc.errorm ~loc:(qloc q) "Not a record field: %a" print_qualid q
        end
    | Ptree.Ptuple pl ->
        let pl = List.map (fun p -> dpattern uc p) pl in
        DPlapp (fs_tuple (List.length pl), pl)
    | Ptree.Pcast (p, pty) -> DPcast (dpattern uc p, ity_of_pty uc pty)
    | Ptree.Pas (p, x) -> DPas (dpattern uc p, create_user_id x)
    | Ptree.Por (p, q) -> DPor (dpattern uc p, dpattern uc q))

(* specifications *)

type lenv = {
  uc     : module_uc;
  th_at  : Theory.theory_uc;
  th_old : Theory.theory_uc;
}

let create_lenv uc = {
  uc     = uc;
  th_at  = Theory.use_export (get_theory uc) Mlw_wp.th_mark_at;
  th_old = Theory.use_export (get_theory uc) Mlw_wp.th_mark_old;
}

let find_global_vs uc p = try match uc_find_ps uc p with
  | PV pv -> Some pv.pv_vs | _ -> None with _ -> None

let find_local_vs uc lvm p = match p with
  | Qdot _ -> find_global_vs uc p
  | Qident id -> let ovs = Mstr.find_opt id.id_str lvm in
      if ovs = None then find_global_vs uc p else ovs

let check_at f0 =
  let tvs0 = t_vars f0 in
  let rec check () f = match f.t_node with
    | Term.Tapp (ls, _) when ls_equal ls fs_at || ls_equal ls fs_old ->
        let tvs = t_vars f in
        if not (Mvs.set_submap tvs tvs0) then Loc.errorm ?loc:f.t_loc
          "locally bound variable %a under `at'/`old'"
          Pretty.print_vs (fst (Mvs.choose (Mvs.set_diff tvs tvs0)));
        t_fold check () f
    | _ ->
        t_fold check () f
  in
  check () f0

let type_term uc th lvm t =
  let gvars p = find_local_vs uc lvm p in
  let t = Typing.type_term th gvars t in
  check_at t; count_term_tuples t; t

let type_fmla uc th lvm f =
  let gvars p = find_local_vs uc lvm p in
  let f = Typing.type_fmla th gvars f in
  check_at f; count_term_tuples f; f

let dpre lenv pl lvm =
  let dpre f = type_fmla lenv.uc lenv.th_at lvm f in
  List.map dpre pl

let dpost lenv ql lvm ty =
  let dpost (loc,pfl) = match pfl with
    | [{ pat_desc = Ptree.Pwild | Ptree.Ptuple [] }, f] ->
        None, Loc.try3 ~loc type_fmla lenv.uc lenv.th_old lvm f
    | [{ pat_desc = Ptree.Pvar id }, f] ->
        let v = create_vsymbol (create_user_id id) ty in
        let lvm = Mstr.add id.id_str v lvm in
        Some v, Loc.try3 ~loc type_fmla lenv.uc lenv.th_old lvm f
    | _ ->
        let v = create_vsymbol (id_fresh "result") ty in
        let i = { id_str = "(null)"; id_loc = loc; id_lab = [] } in
        let t = { term_desc = Tident (Qident i); term_loc = loc } in
        let f = { term_desc = Tmatch (t, pfl); term_loc = loc } in
        let lvm = Mstr.add "(null)" v lvm in
        Some v, Loc.try3 ~loc type_fmla lenv.uc lenv.th_old lvm f
  in
  List.map dpost ql

let find_xsymbol uc p = match uc_find_ps uc p with XS xs -> xs
  | _ -> Loc.errorm ~loc:(qloc p) "exception symbol expected"

let dxpost lenv ql lvm =
  let add_exn (q,pat,f) m =
    let xs = find_xsymbol lenv.uc q in
    Mexn.change (function
      | Some l -> Some ((pat,f) :: l)
      | None   -> Some ((pat,f) :: [])) xs m in
  let mk_xpost loc xs pfl =
    dpost lenv [loc,pfl] lvm (ty_of_ity xs.xs_ity) in
  let exn_map (loc,xpfl) =
    let m = List.fold_right add_exn xpfl Mexn.empty in
    Mexn.mapi (fun xs pfl -> mk_xpost loc xs pfl) m in
  let add_map ql m =
    Mexn.union (fun _ l r -> Some (l @ r)) (exn_map ql) m in
  List.fold_right add_map ql Mexn.empty

let dreads lenv rl lvm =
  let dreads q = match find_local_vs lenv.uc lvm q with Some vs -> vs
    | None -> Loc.errorm ~loc:(qloc q) "Not a variable: %a" print_qualid q in
  List.map dreads rl

let dwrites lenv wl lvm =
  let dwrites t = type_term lenv.uc (get_theory lenv.uc) lvm t in
  List.map dwrites wl

let find_variant_ls uc p = match uc_find_ls uc p with
  | { ls_args = [u;v]; ls_value = None } as ls when ty_equal u v -> ls
  | s -> Loc.errorm ~loc:(qloc p) "Not an order relation: %a" Pretty.print_ls s

let dvariant lenv varl lvm =
  let dvar t = type_term lenv.uc lenv.th_at lvm t in
  let dvar (t,q) = dvar t, Opt.map (find_variant_ls lenv.uc) q in
  List.map dvar varl

let dspec lenv sp lvm ty = {
  ds_pre     = dpre lenv sp.sp_pre lvm;
  ds_post    = dpost lenv sp.sp_post lvm ty;
  ds_xpost   = dxpost lenv sp.sp_xpost lvm;
  ds_reads   = dreads lenv sp.sp_reads lvm;
  ds_writes  = dwrites lenv sp.sp_writes lvm;
  ds_variant = dvariant lenv sp.sp_variant lvm;
  ds_checkrw = sp.sp_checkrw;
  ds_diverge = sp.sp_diverge;
}

let dassert lenv f lvm =
  type_fmla lenv.uc lenv.th_at lvm f

let dinvariant = dpre

let dloopannot lenv ann lvm =
  dvariant   lenv ann.loop_variant   lvm,
  dinvariant lenv ann.loop_invariant lvm

(* abstract values *)

let dbinder uc id gh pty =
  let id = Opt.map create_user_id id in
  let otv = Opt.fold opaque_tvs Stv.empty pty in
  let dity = match pty with
    | Some pty -> dity_of_ity (ity_of_pty ~noop:false uc pty)
    | None -> dity_fresh () in
  id, gh, otv, dity

let dparam uc (_,id,gh,pty) = dbinder uc id gh (Some pty)
let dbinder uc (_,id,gh,pty) = dbinder uc id gh pty

let rec dtype_c lenv (tyv, sp) = dtype_v lenv tyv, dspec lenv sp

and dtype_v lenv = function
  | PTpure pty ->
      DSpecV (dity_of_ity (ity_of_pty lenv.uc pty))
  | PTfunc (bl,tyc) ->
      DSpecA (List.map (fun p -> dparam lenv.uc p) bl, dtype_c lenv tyc)

(* expressions *)

let add_lemma_label ~top id = function
  | Gnone -> id, false
  | Gghost -> id, true
  | Glemma when not top ->
      Loc.errorm ~loc:id.id_loc "lemma functions are only allowed at toplevel"
  | Glemma -> { id with id_lab = Lstr Mlw_wp.lemma_label :: id.id_lab }, true

let is_reusable de = match de.de_node with
  | DEvar _ | DEgpvar _ | DEconst _ | DEtrue | DEfalse -> true
  | DEplapp ({pl_value = {fd_ity = ity; fd_mut = None}},[]) ->
      ity_immutable ity (* cannot reuse since regions will not be shared *)
  | DElsapp (_,[]) -> true (* can reuse since dvty is shared and immutable *)
  | _ -> false

let mk_var n de =
  Mlw_dexpr.dexpr ?loc:de.de_loc (DEvar (n, de.de_dvty))

let mk_let ~loc n de node =
  let de1 = Mlw_dexpr.dexpr ~loc node in
  DElet ((id_user n loc, false, de), de1)

let chainable_ps = function
  | { ps_aty = { aty_args = [pv1;pv2]; aty_result = VTvalue ity }}
  | { ps_aty = { aty_args = [pv1]; aty_result =
       VTarrow { aty_args = [pv2]; aty_result = VTvalue ity }}} ->
      ity_equal ity ity_bool
      && not (ity_equal pv1.pv_ity ity_bool)
      && not (ity_equal pv2.pv_ity ity_bool)
  | _ -> false

let chainable_qualid uc p = match uc_find_ps uc p with
  | PS ps -> chainable_ps ps
  | LS { ls_args = [ty1;ty2]; ls_value = ty } ->
      Opt.fold (fun _ ty -> ty_equal ty ty_bool) true ty
      && not (ty_equal ty1 ty_bool)
      && not (ty_equal ty2 ty_bool)
  | LS _ | PL _ | PV _ | XS _ -> false

let chainable_op uc denv op =
  (* non-bool -> non-bool -> bool *)
  op.id_str = "infix =" || op.id_str = "infix <>" ||
  match denv_get_opt denv op.id_str with
  | Some (DEvar (_,t)) -> dvty_is_chainable t
  | Some (DEgpsym ps) -> chainable_ps ps
  | Some _ -> false (* can never happen *)
  | None -> chainable_qualid uc (Qident op)

let mk_closure loc _ls =
  Loc.errorm ~loc "Partial@ application@ of@ logical@ symbols@ \
    is@ currently@ not@ supported@ in@ programs."
(*
  let mk dt = Dterm.dterm ~loc dt in
  let id = id_user "fc" loc and dty = dty_fresh () in
  let mk_v i _ =
    id_user ("y" ^ string_of_int i) loc, dty_fresh () in
  let mk_t (id, dty) = mk (DTvar (id.pre_name, dty)) in
  let vl = Lists.mapi mk_v ls.ls_args in
  let tl = List.map mk_t vl in
  let app e1 e2 = DTapp (fs_func_app, [mk e1; e2]) in
  let e = List.fold_left app (DTvar ("fc", dty)) tl in
  let f = DTapp (ps_equ, [mk e; mk (DTapp (ls, tl))]) in
  DTeps (id, dty, mk (DTquant (Tforall, vl, [], mk f)))
*)

let rec dexpr ({uc = uc} as lenv) denv {expr_desc = desc; expr_loc = loc} =
  let expr_app e el =
    List.fold_left (fun e1 (loc, e2) ->
      DEapply (Mlw_dexpr.dexpr ~loc e1, e2)) e el
  in
  let rec apply_pl loc pl al l el = match l, el with
    | (_::l), (e::el) -> apply_pl loc pl (e::al) l el
    | [], _ -> expr_app (DEplapp (pl, List.rev_map snd al)) el
    | _, [] -> expr_app (mk_closure loc pl) (List.rev_append al el)
  in
  let rec apply_ls loc ls al l el = match l, el with
    | (_::l), (e::el) -> apply_ls loc ls (e::al) l el
    | [], _ -> expr_app (DElsapp (ls, List.rev_map snd al)) el
    | _, [] -> expr_app (mk_closure loc ls) (List.rev_append al el)
  in
  let qualid_app q el = match uc_find_ps uc q with
    | PV pv -> expr_app (DEgpvar pv) el
    | PS ps -> expr_app (DEgpsym ps) el
    | PL pl -> apply_pl (qloc q) pl [] pl.pl_args el
    | LS ls -> apply_ls (qloc q) ls [] ls.ls_args el
    | XS xs -> Loc.errorm ~loc:(qloc q)
        "unexpected exception symbol %a" print_xs xs
  in
  let qualid_app q el = match q with
    | Qident {id_str = n} ->
        (match denv_get_opt denv n with
        | Some d -> expr_app d el
        | None -> qualid_app q el)
    | _ -> qualid_app q el
  in
  let rec unfold_app e1 e2 el = match e1.expr_desc with
    | Ptree.Eapply (e11,e12) ->
        let e12 = dexpr lenv denv e12 in
        unfold_app e11 e12 ((e1.expr_loc, e2)::el)
    | Ptree.Eident q ->
        qualid_app q ((e1.expr_loc, e2)::el)
    | _ ->
        expr_app (DEapply (dexpr lenv denv e1, e2)) el
  in
  Mlw_dexpr.dexpr ~loc (match desc with
  | Ptree.Eident q ->
      qualid_app q []
  | Ptree.Eidapp (q, tl) ->
      (* FIXME: qloc q is wrong for the 2nd and later arguments *)
      let loc = qloc q in
      qualid_app q (List.map (fun t -> loc, dexpr lenv denv t) tl)
  | Ptree.Eapply (e1, e2) ->
      unfold_app e1 (dexpr lenv denv e2) []
  | Ptree.Etuple el ->
      let el = List.map (dexpr lenv denv) el in
      DElsapp (fs_tuple (List.length el), el)
  | Ptree.Einfix (e12, op2, e3)
  | Ptree.Einnfix (e12, op2, e3) ->
      let make_app de1 op de2 = if op.id_str = "infix <>" then
        let oq = Qident { op with id_str = "infix =" } in
        (* FIXME: op.id_loc is wrong for the 2nd argument *)
        let dt = qualid_app oq [(op.id_loc, de1); (op.id_loc, de2)] in
        DEnot (Mlw_dexpr.dexpr ~loc dt)
      else
        qualid_app (Qident op) [(op.id_loc, de1); (op.id_loc, de2)]
      in
      let rec make_chain n1 n2 de1 = function
        | [op,de2] ->
            make_app de1 op de2
        | (op,de2) :: ch ->
            let re = is_reusable de2 in
            let v = if re then de2 else mk_var n1 de2 in
            let de12 = Mlw_dexpr.dexpr ~loc (make_app de1 op v) in
            let de23 = Mlw_dexpr.dexpr ~loc (make_chain n2 n1 v ch) in
            let d = DElazy (DEand, de12, de23) in
            if re then d else mk_let ~loc n1 de2 d
        | [] -> assert false in
      let rec get_chain e12 acc = match e12.expr_desc with
        | Ptree.Einfix (e1, op1, e2) when chainable_op uc denv op1 ->
            get_chain e1 ((op1, dexpr lenv denv e2) :: acc)
        | _ -> e12, acc in
      let ch = [op2, dexpr lenv denv e3] in
      let e1, ch = if chainable_op uc denv op2
        then get_chain e12 ch else e12, ch in
      make_chain "q1 " "q2 " (dexpr lenv denv e1) ch
  | Ptree.Econst (Number.ConstInt _ as c) -> DEconst (c, ity_int)
  | Ptree.Econst (Number.ConstReal _ as c) -> DEconst (c, ity_real)
  | Ptree.Erecord [] -> raise Decl.EmptyRecord
  | Ptree.Erecord ((q,_)::_ as fl) ->
      let prog_val cs pj = function
        | None -> Loc.error ~loc (Decl.RecordFieldMissing (cs.pl_ls,pj.pl_ls))
        | Some e -> dexpr lenv denv e in
      let pure_val cs pj = function
        | None -> Loc.error ~loc (Decl.RecordFieldMissing (cs,pj))
        | Some e -> dexpr lenv denv e in
      begin match uc_find_ps uc q with
      | PL _ -> let cs,fl = prog_record ~loc uc prog_val fl in DEplapp (cs,fl)
      | LS _ -> let cs,fl = pure_record ~loc uc pure_val fl in DElsapp (cs,fl)
      | _ -> Loc.errorm ~loc:(qloc q) "Not a record field: %a" print_qualid q
      end
  | Ptree.Eupdate (_, []) -> raise Decl.EmptyRecord
  | Ptree.Eupdate (e1, ((q,_)::_ as fl)) ->
      let e1 = dexpr lenv denv e1 in
      let re = is_reusable e1 in
      let v = if re then e1 else mk_var "_q " e1 in
      let prog_val _ pj = function
        | None -> Mlw_dexpr.dexpr ~loc (DEplapp (pj, [v]))
        | Some e -> dexpr lenv denv e in
      let pure_val _ pj = function
        | None -> Mlw_dexpr.dexpr ~loc (DElsapp (pj, [v]))
        | Some e -> dexpr lenv denv e in
      let d = match uc_find_ps uc q with
        | PL _ -> let cs,fl = prog_record ~loc uc prog_val fl in DEplapp (cs,fl)
        | LS _ -> let cs,fl = pure_record ~loc uc pure_val fl in DElsapp (cs,fl)
        | _ -> Loc.errorm ~loc:(qloc q) "Not a record field: %a" print_qualid q
      in
      if re then d else mk_let ~loc "_q " e1 d
  | Ptree.Elet (id, gh, e1, e2) ->
      let id, gh = add_lemma_label ~top:false id gh in
      let ld = create_user_id id, gh, dexpr lenv denv e1 in
      DElet (ld, dexpr lenv (denv_add_let denv ld) e2)
  | Ptree.Efun (id, gh, lam, e2) ->
      let id, gh = add_lemma_label ~top:false id gh in
      let bl, de, sp = dlambda lenv denv lam in
      let fd = create_user_id id, gh, bl, de, sp in
      DEfun (fd, dexpr lenv (denv_add_fun denv fd) e2)
  | Ptree.Erec (fdl, e1) ->
      let denv, rd = drec_defn ~top:false lenv denv fdl in
      DErec (rd, dexpr lenv denv e1)
  | Ptree.Elam lam ->
      let bl, de, sp = dlambda lenv denv lam in
      DElam (bl, de, sp)
  | Ptree.Ematch (e1, bl) ->
      let e1 = dexpr lenv denv e1 in
      let branch (pp, e) =
        let pp = dpattern uc pp in
        let denv = denv_add_pat denv pp in
        pp, dexpr lenv denv e in
      DEcase (e1, List.map branch bl)
  | Ptree.Eif (e1, e2, e3) ->
      let e1 = dexpr lenv denv e1 in
      let e2 = dexpr lenv denv e2 in
      let e3 = dexpr lenv denv e3 in
      DEif (e1, e2, e3)
  | Ptree.Enot e1 ->
      DEnot (dexpr lenv denv e1)
  | Ptree.Elazy (e1, op, e2) ->
      let op = match op with
        | Ptree.LazyAnd -> DEand
        | Ptree.LazyOr  -> DEor in
      let e1 = dexpr lenv denv e1 in
      let e2 = dexpr lenv denv e2 in
      DElazy (op, e1, e2)
  | Ptree.Etrue -> DEtrue
  | Ptree.Efalse -> DEfalse
  | Ptree.Esequence (e1, e2) ->
      let e1 = dexpr lenv denv e1 in
      let e2 = dexpr lenv denv e2 in
      DElet ((id_user "_" loc, false, e1), e2)
  | Ptree.Eloop (ann, e1) ->
      let e1 = dexpr lenv denv e1 in
      DEloop (dloopannot lenv ann, e1)
  | Ptree.Ewhile (e1, ann, e2) ->
      let e1 = dexpr lenv denv e1 in
      let e2 = dexpr lenv denv e2 in
      DEwhile (e1, dloopannot lenv ann, e2)
  | Ptree.Efor (id, efrom, dir, eto, inv, e1) ->
      let dir = match dir with
        | Ptree.To -> To | Ptree.Downto -> DownTo in
      let efrom = dexpr lenv denv efrom in
      let eto = dexpr lenv denv eto in
      let inv = dinvariant lenv inv in
      let id = create_user_id id in
      let denv = denv_add_var denv id (dity_of_ity ity_int) in
      DEfor (id, efrom, dir, eto, inv, dexpr lenv denv e1)
  | Ptree.Eassign (e1, q, e2) ->
      let pl = match uc_find_ps uc q with PL pl -> pl | _ ->
        Loc.errorm ~loc:(qloc q) "%a is not a field name" print_qualid q in
      DEassign (pl, dexpr lenv denv e1, dexpr lenv denv e2)
  | Ptree.Eraise (q, e1) ->
      let xs = find_xsymbol uc q in
      let e1 = match e1 with
        | Some e1 -> dexpr lenv denv e1
        | None when ity_equal xs.xs_ity ity_unit ->
            Mlw_dexpr.dexpr ~loc (DElsapp (Mlw_expr.fs_void, []))
        | _ -> Loc.errorm ~loc "exception argument expected" in
      DEraise (xs, e1)
  | Ptree.Etry (e1, cl) ->
      let e1 = dexpr lenv denv e1 in
      let branch (q, pp, e) =
        let xs = find_xsymbol uc q in
        let pp = match pp with
          | Some pp -> dpattern uc pp
          | None when ity_equal xs.xs_ity ity_unit ->
              Mlw_dexpr.dpattern ~loc (DPlapp (Mlw_expr.fs_void, []))
          | _ -> Loc.errorm ~loc "exception argument expected" in
        let denv = denv_add_pat denv pp in
        let e = dexpr lenv denv e in
        xs, pp, e in
      DEtry (e1, List.map branch cl)
  | Ptree.Eghost e1 ->
      DEghost (dexpr lenv denv e1)
  | Ptree.Eany (tyv, sp) ->
      let dsp = if
        sp.sp_pre   = [] && sp.sp_post   = [] && sp.sp_xpost   = [] &&
        sp.sp_reads = [] && sp.sp_writes = [] && sp.sp_variant = [] &&
        not sp.sp_checkrw && not sp.sp_diverge
      then None
      else Some (dspec lenv sp) in
      DEany (dtype_v lenv tyv, dsp)
  | Ptree.Eabstract (e1, sp) ->
      DEabstract (dexpr lenv denv e1, dspec lenv sp)
  | Ptree.Eabsurd -> DEabsurd
  | Ptree.Eassert (ak, lexpr) ->
      let ak = match ak with
        | Ptree.Aassert -> Aassert
        | Ptree.Aassume -> Aassume
        | Ptree.Acheck  -> Acheck in
      DEassert (ak, dassert lenv lexpr)
  | Ptree.Emark (id, e1) ->
      DEmark (create_user_id id, dexpr lenv denv e1)
  | Ptree.Enamed (Lpos uloc, e1) ->
      DEuloc (dexpr lenv denv e1, uloc)
  | Ptree.Enamed (Lstr lab, e1) ->
      DElabel (dexpr lenv denv e1, Slab.singleton lab)
  | Ptree.Ecast (e1, pty) ->
      (* FIXME: accepts and silently ignores double casts: ((0:ty1):ty2) *)
      let e1 = dexpr lenv denv e1 in
      let ity = ity_of_pty uc pty in
      match e1.de_node with
      | DEconst (c, _) -> DEconst (c, ity)
      | _ -> DEcast (e1, ity))

and drec_defn ~top lenv denv fdl =
  let prep (id, gh, (bl, pty, e, sp)) =
    let id, gh = add_lemma_label ~top id gh in
    let bl = List.map (dbinder lenv.uc) bl in
    let dity = match pty with
      | Some pty -> dity_of_ity (ity_of_pty lenv.uc pty)
      | None -> dity_fresh () in
    let pre denv = dexpr lenv denv e, dspec lenv sp in
    create_user_id id, gh, bl, dity, pre in
  Mlw_dexpr.drec_defn denv (List.map prep fdl)

and dlambda lenv denv (bl, pty, e1, sp) =
  let bl = List.map (dbinder lenv.uc) bl in
  let e1 = match pty with
    | Some pty -> { e1 with expr_desc = Ecast (e1, pty) }
    | None -> e1 in
  let e1 = dexpr lenv (denv_add_args denv bl) e1 in
  bl, e1, dspec lenv sp

(** Type declaration *)

let add_type_invariant loc uc id params inv =
  let x = "self" in
  let its = match uc_find_ts uc (Qident id) with
    | PT its when its.its_inv -> its
    | _ -> Loc.errorm ~loc "type %s does not have an invariant" id.id_str in
  let add_tv acc { id_str = id; id_loc = loc } =
    let e = Loc.Located (loc, DuplicateTypeVar id) in
    Sstr.add_new e id acc, tv_of_string id in
  let _, tvl = Lists.map_fold_left add_tv Sstr.empty params in
  let ty = ty_app its.its_ts (List.map ty_var tvl) in
  let res = create_vsymbol (id_fresh x) ty in
  let find = function
    | Qident { id_str = id } when id = x -> Some res
    | _ -> None in
  let mk_inv f =
    let f = Typing.type_fmla (get_theory uc) find f in
    t_label_add Split_goal.stop_split f in
  let inv = List.map mk_inv inv in
  let q = Mlw_ty.create_post res (t_and_simp_l inv) in
  let q = if List.for_all2 tv_equal its.its_ts.ts_args tvl then q else
    let add mtv u v = Mtv.add u (ty_var v) mtv in
    let mtv = List.fold_left2 add Mtv.empty tvl its.its_ts.ts_args in
    t_ty_subst mtv Mvs.empty q in
  let uc = (count_term_tuples q; flush_tuples uc) in
  Mlw_module.add_invariant uc its q

let look_for_loc tdl s =
  let look_id loc id = if id.id_str = s then Some id.id_loc else loc in
  let look_pj loc (_,id,_,_) = Opt.fold look_id loc id in
  let look_cs loc (csloc,id,pjl) =
    let loc = if id.id_str = s then Some csloc else loc in
    List.fold_left look_pj loc pjl in
  let look_fl loc f = look_id loc f.f_ident in
  let look loc d =
    let loc = look_id loc d.td_ident in
    match d.td_def with
      | TDabstract | TDalias _ | TDrange _ | TDfloat _ -> loc
      | TDalgebraic csl -> List.fold_left look_cs loc csl
      | TDrecord fl -> List.fold_left look_fl loc fl
  in
  List.fold_left look None tdl

let add_types ~wp uc tdl =
  let add m d =
    let id = d.td_ident.id_str in
    Mstr.add_new (Loc.Located (d.td_loc, ClashSymbol id)) id d m in
  let def = List.fold_left add Mstr.empty tdl in

  (* detect cycles *)

  let rec cyc_visit x d seen = match Mstr.find_opt x seen with
    | Some true -> seen
    | Some false -> Loc.errorm ~loc:d.td_loc "Cyclic type definition"
    | None ->
        let ts_seen seen = function
          | Qident { id_str = x } ->
              begin try cyc_visit x (Mstr.find x def) seen
              with Not_found -> seen end
          | _ -> seen in
        let rec check seen = function
          | PTtyvar _ -> seen
          | PTparen ty -> check seen ty
          | PTarrow (ty1,ty2) -> check (check seen ty1) ty2
          | PTtyapp (q,tyl) -> List.fold_left check (ts_seen seen q) tyl
          | PTtuple tyl -> List.fold_left check seen tyl in
        let seen = match d.td_def with
          | TDabstract | TDrange _ | TDfloat _ | TDalgebraic _ | TDrecord _ ->
              seen
          | TDalias ty -> check (Mstr.add x false seen) ty in
        Mstr.add x true seen in
  ignore (Mstr.fold cyc_visit def Mstr.empty);

  (* detect impure types *)

  let impures = Hstr.create 5 in
  let rec imp_visit x =
    try Hstr.find impures x
    with Not_found ->
      let ts_imp = function
        | Qident { id_str = x } when Mstr.mem x def -> imp_visit x
        | q ->
            begin match uc_find_ts uc q with
              | PT _ -> true | TS _ -> false
            end
      in
      let rec check = function
        | PTtyvar _ -> false
        | PTparen ty -> check ty
        | PTarrow (ty1,ty2) -> check ty1 || check ty2
        | PTtyapp (q,tyl) -> ts_imp q || List.exists check tyl
        | PTtuple tyl -> List.exists check tyl in
      Hstr.replace impures x false;
      let imp =
        let td = Mstr.find x def in
        match td.td_def with
        | TDabstract | TDrange _ | TDfloat _ -> false
        | TDalias ty -> check ty
        | TDalgebraic csl ->
            let check (_,_,gh,ty) = gh || check ty in
            let cons (_,_,l) = List.exists check l in
            td.td_inv <> [] || td.td_vis <> Public || List.exists cons csl
        | TDrecord fl ->
            let field f = f.f_ghost || f.f_mutable || check f.f_pty in
            td.td_inv <> [] || td.td_vis <> Public || List.exists field fl
      in
      Hstr.replace impures x imp;
      imp
  in
  Mstr.iter (fun x _ -> ignore (imp_visit x)) def;

  (* detect mutable types and invariants *)

  let mutables = Hstr.create 5 in
  let rec mut_visit x =
    try Hstr.find mutables x
    with Not_found ->
      let ts_mut = function
        | Qident { id_str = x } when Mstr.mem x def -> mut_visit x
        | q ->
            begin match uc_find_ts uc q with
              | PT its -> its.its_regs <> [] || its.its_inv
              | TS _ -> false
            end
      in
      let rec check = function
        | PTtyvar _ -> false
        | PTparen ty -> check ty
        | PTarrow (ty1,ty2) -> check ty1 || check ty2
        | PTtyapp (q,tyl) -> ts_mut q || List.exists check tyl
        | PTtuple tyl -> List.exists check tyl in
      Hstr.replace mutables x false;
      let mut =
        let td = Mstr.find x def in
        match td.td_def with
        | TDabstract | TDrange _ | TDfloat _ -> false
        | TDalias ty -> check ty
        | TDalgebraic csl ->
            let check (_,_,_,ty) = check ty in
            let cons (_,_,l) = List.exists check l in
            td.td_inv <> [] || List.exists cons csl
        | TDrecord fl ->
            let field f = f.f_mutable || check f.f_pty in
            td.td_inv <> [] || List.exists field fl
      in
      Hstr.replace mutables x mut;
      mut
  in
  Mstr.iter (fun x _ -> ignore (mut_visit x)) def;

  (* create type symbols and predefinitions for mutable types *)

  let mk_field ity gh mut = { fd_ity = ity; fd_ghost = gh; fd_mut = mut } in

  let tysymbols = Hstr.create 5 in
  let predefs = Hstr.create 5 in
  let rec its_visit x =
    try match Hstr.find tysymbols x with
      | Some ts -> ts
      | None ->
          let td = Mstr.find x def in let loc = td.td_loc in
          if td.td_inv <> []
          then Loc.errorm ~loc "Recursive types cannot have invariants"
          else Loc.errorm ~loc "Recursive types cannot have mutable components"
    with Not_found ->
      let d = Mstr.find x def in
      let add_tv acc id =
        let e = Loc.Located (id.Ptree.id_loc, DuplicateTypeVar id.id_str) in
        let tv = tv_of_string id.id_str in
        Mstr.add_new e id.id_str tv acc in
      let vars = List.fold_left add_tv Mstr.empty d.td_params in
      let vl = List.map (fun id -> Mstr.find id.id_str vars) d.td_params in
      let id = Typing.create_user_id d.td_ident in
      let abst = d.td_vis = Abstract in
      let priv = d.td_vis = Private in
      Hstr.add tysymbols x None;
      let get_ts = function
        | Qident { id_str = x } when Mstr.mem x def -> its_visit x
        | q -> uc_find_ts uc q
      in
      let rec parse = function
        | PTtyvar ({ id_loc = loc }, true) -> Loc.errorm ~loc
            "Opaqueness@ annotations@ are@ only@ \
              allowed@ in@ function@ and@ predicate@ prototypes"
        | PTtyvar ({ id_str = v ; id_loc = loc }, _) ->
            let e = Loc.Located (loc, UnboundTypeVar v) in
            ity_var (Mstr.find_exn e v vars)
        | PTtyapp (q,tyl) ->
            let tyl = List.map parse tyl in
            begin match get_ts q with
              | TS ts -> Loc.try2 ~loc:(qloc q) ity_pur ts tyl
              | PT ts -> Loc.try2 ~loc:(qloc q) ity_app_fresh ts tyl
            end
        | PTtuple tyl ->
            let ts = ts_tuple (List.length tyl) in
            ity_pur ts (List.map parse tyl)
        | PTarrow (ty1,ty2) ->
            ity_pur ts_func [parse ty1; parse ty2]
        | PTparen ty ->
            parse ty
      in
      let ts = match d.td_def with
        | TDalias _ when abst || priv -> Loc.errorm ~loc:d.td_loc
            "type aliases cannot be abstract or private"
        | TDalias _ when d.td_inv <> [] -> Loc.errorm ~loc:d.td_loc
            "type aliases cannot have invariants"
        | TDalias ty when Hstr.find impures x ->
            let def = parse ty in
            let nogh = ity_nonghost_reg Sreg.empty def in
            let ghost_reg = Sreg.diff def.ity_vars.vars_reg nogh in
            let rl = Sreg.elements def.ity_vars.vars_reg in
            PT (create_itysymbol id
              ~abst ~priv ~inv:false ~ghost_reg vl rl (Some def))
        | TDalias ty ->
            let def = ty_of_ity (parse ty) in
            TS (create_tysymbol id vl (Alias def))
        | TDalgebraic csl when Hstr.find mutables x ->
            let projs = Hstr.create 5 in
            let nogh = ref Sreg.empty in
            (* to check projections' types we must fix the tyvars *)
            let add s v = let t = ity_var v in ity_match s t t in
            let sbs = List.fold_left add ity_subst_empty vl in
            let mk_proj (regs,inv) (_loc,id,gh,pty) =
              let ity = parse pty in
              let fd = mk_field ity gh None in
              let inv = inv || ity_has_inv ity in
              match id with
              | None ->
                  if not gh then nogh := ity_nonghost_reg !nogh ity;
                  let regs = Sreg.union regs ity.ity_vars.vars_reg in
                  (regs, inv), (None, fd)
              | Some ({ id_str = x; id_loc = loc } as id) ->
                  try
                    let fd = Hstr.find projs x in
                    if gh <> fd.fd_ghost then Loc.errorm ~loc
                      "this field must be ghost in every constructor";
                    ignore (Loc.try3 ~loc ity_match sbs fd.fd_ity ity);
                    (regs, inv), (Some (Typing.create_user_id id), fd)
                  with Not_found ->
                    Hstr.replace projs x fd;
                    if not gh then nogh := ity_nonghost_reg !nogh ity;
                    let regs = Sreg.union regs ity.ity_vars.vars_reg in
                    (regs, inv), (Some (Typing.create_user_id id), fd)
            in
            let mk_constr s (_loc,cid,pjl) =
              let s,pjl = Lists.map_fold_left mk_proj s pjl in
              s, (Typing.create_user_id cid, pjl)
            in
            let init = (Sreg.empty, d.td_inv <> []) in
            let (regs,inv),def = Lists.map_fold_left mk_constr init csl in
            let ghost_reg = Sreg.diff regs !nogh in
            let rl = Sreg.elements regs in
            Hstr.replace predefs x def;
            PT (create_itysymbol id ~abst ~priv ~inv ~ghost_reg vl rl None)
        | TDrecord fl when Hstr.find mutables x ->
            let nogh = ref Sreg.empty in
            let mk_field (regs,inv) f =
              let ity = parse f.f_pty in
              let inv = inv || ity_has_inv ity in
              let fid = Typing.create_user_id f.f_ident in
              let regs,mut = if f.f_mutable then
                let r = create_region fid ity in
                Sreg.add r regs, Some r
              else
                Sreg.union regs ity.ity_vars.vars_reg, None
              in
              if not f.f_ghost then nogh :=
                Opt.fold_right Sreg.add mut (ity_nonghost_reg !nogh ity);
              (regs, inv), (Some fid, mk_field ity f.f_ghost mut)
            in
            let init = (Sreg.empty, d.td_inv <> []) in
            let (regs,inv),pjl = Lists.map_fold_left mk_field init fl in
            let ghost_reg = Sreg.diff regs !nogh in
            let rl = Sreg.elements regs in
            let cid = { d.td_ident with id_str = "mk " ^ d.td_ident.id_str } in
            Hstr.replace predefs x [Typing.create_user_id cid, pjl];
            PT (create_itysymbol id ~abst ~priv ~inv ~ghost_reg vl rl None)
        | TDalgebraic _ | TDrecord _ when Hstr.find impures x ->
            PT (create_itysymbol id ~abst ~priv ~inv:false vl [] None)
        | TDalgebraic _ | TDrecord _ | TDabstract ->
            TS (create_tysymbol id vl NoDef)
        | TDrange (lo,hi) ->
            let ir = { Number.ir_lower = lo;
                       Number.ir_upper = hi } in
            TS (Loc.try2 ~loc:d.td_loc create_tysymbol id vl (Range ir))
        | TDfloat (eb,sb) ->
            let fp = { Number.fp_exponent_digits = eb;
                       Number.fp_significand_digits = sb } in
            TS (Loc.try2 ~loc:d.td_loc create_tysymbol id vl (Float fp))
      in
      Hstr.add tysymbols x (Some ts);
      ts
  in
  Mstr.iter (fun x _ -> ignore (its_visit x)) def;

  (* create predefinitions for immutable types *)

  let def_visit d (abstr,algeb,alias) =
    let x = d.td_ident.id_str in
    let ts = Opt.get (Hstr.find tysymbols x) in
    let vl = match ts with
      | PT s -> s.its_ts.ts_args | TS s -> s.ts_args in
    let add_tv s x v = Mstr.add x.id_str v s in
    let vars = List.fold_left2 add_tv Mstr.empty d.td_params vl in
    let get_ts = function
      | Qident { id_str = x } when Mstr.mem x def ->
          Opt.get (Hstr.find tysymbols x)
      | q -> uc_find_ts uc q
    in
    let rec parse = function
      | PTtyvar ({ id_loc = loc }, true) -> Loc.errorm ~loc
          "Opaqueness@ annotations@ are@ only@ \
            allowed@ in@ function@ and@ predicate@ prototypes"
      | PTtyvar ({ id_str = v ; id_loc = loc }, _) ->
          let e = Loc.Located (loc, UnboundTypeVar v) in
          ity_var (Mstr.find_exn e v vars)
      | PTtyapp (q,tyl) ->
          let tyl = List.map parse tyl in
          begin match get_ts q with
            | TS ts -> Loc.try2 ~loc:(qloc q) ity_pur ts tyl
            | PT ts -> Loc.try3 ~loc:(qloc q) ity_app ts tyl []
          end
      | PTtuple tyl ->
          let ts = ts_tuple (List.length tyl) in
          ity_pur ts (List.map parse tyl)
      | PTarrow (ty1,ty2) ->
          ity_pur ts_func [parse ty1; parse ty2]
      | PTparen ty ->
          parse ty
    in
    match d.td_def with
      | TDabstract | TDrange _ | TDfloat _ ->
          ts :: abstr, algeb, alias
      | TDalias _ ->
          abstr, algeb, ts :: alias
      | (TDalgebraic _ | TDrecord _) when Hstr.find mutables x ->
          abstr, (ts, Hstr.find predefs x) :: algeb, alias
      | TDalgebraic csl ->
          let projs = Hstr.create 5 in
          let mk_proj (_loc,id,gh,pty) =
            let ity = parse pty in
            let fd = mk_field ity gh None in
            match id with
            | None -> None, fd
            | Some ({ id_str = x; id_loc = loc } as id) ->
                try
                  let fd = Hstr.find projs x in
                  if gh <> fd.fd_ghost then Loc.errorm ~loc
                    "this field must be ghost in every constructor";
                  Loc.try2 ~loc ity_equal_check fd.fd_ity ity;
                  Some (Typing.create_user_id id), fd
                with Not_found ->
                  Hstr.replace projs x fd;
                  Some (Typing.create_user_id id), fd
          in
          let mk_constr (_loc,cid,pjl) =
            Typing.create_user_id cid, List.map mk_proj pjl in
          abstr, (ts, List.map mk_constr csl) :: algeb, alias
      | TDrecord fl ->
          let mk_field f =
            let fid = Typing.create_user_id f.f_ident in
            Some fid, mk_field (parse f.f_pty) f.f_ghost None in
          let cid = { d.td_ident with id_str = "mk " ^ d.td_ident.id_str } in
          let csl = [Typing.create_user_id cid, List.map mk_field fl] in
          abstr, (ts, csl) :: algeb, alias
  in
  let abstr,algeb,alias = List.fold_right def_visit tdl ([],[],[]) in

  (* create pure type declarations *)

  let mk_pure_decl ts csl =
    let pjt = Hstr.create 3 in
    let constr = List.length csl in
    let opaque = Stv.of_list ts.ts_args in
    let ty = ty_app ts (List.map ty_var ts.ts_args) in
    let mk_proj (pj,fd) =
      let fty = ty_of_ity fd.fd_ity in
      fty, match pj with
        | None -> None
        | Some id ->
            try Hstr.find pjt id.pre_name with Not_found ->
            let pj = Some (create_fsymbol ~opaque id [ty] fty) in
            Hstr.replace pjt id.pre_name pj;
            pj
    in
    let mk_constr (id,pjl) =
      let pjl = List.map mk_proj pjl in
      let cs = create_fsymbol ~opaque ~constr id (List.map fst pjl) ty in
      cs, List.map snd pjl
    in
    List.map mk_constr csl
  in
  let mk_data_decl (s,csl) (alg_pur,alg_imp) = match s with
    | PT its -> alg_pur, (its, csl) :: alg_imp
    | TS ts  -> (ts, mk_pure_decl ts csl) :: alg_pur, alg_imp
  in
  let alg_pur,alg_imp = List.fold_right mk_data_decl algeb ([],[]) in

  (* add type declarations *)

  let add_pure_type_decl uc ts =
    let uc = add_decl_with_tuples uc (Decl.create_ty_decl ts) in
    match ts.ts_def with
    | NoDef | Alias _ -> uc
    | Range rg ->
       Typing.add_range_decl uc add_decl add_meta ts rg
    | Float fmt ->
       Typing.add_float_decl uc add_decl add_meta ts fmt
  in
  let add_type_decl uc = function
    | PT ts -> add_pdecl_with_tuples ~wp uc (create_ty_decl ts)
    | TS ts -> add_pure_type_decl uc ts
  in
  let add_invariant uc d = if d.td_inv = [] then uc else
    add_type_invariant d.td_loc uc d.td_ident d.td_params d.td_inv in
  try
    let uc = List.fold_left add_type_decl uc abstr in
    let uc = if alg_imp = [] then uc else
      add_pdecl_with_tuples ~wp uc (create_data_decl alg_imp) in
    let uc = if alg_pur = [] then uc else
      add_decl_with_tuples uc (Decl.create_data_decl alg_pur) in
    let uc = List.fold_left add_type_decl uc alias in
    let uc = List.fold_left add_invariant uc tdl in
    uc
  with
    | ClashSymbol s ->
        Loc.error ?loc:(look_for_loc tdl s) (ClashSymbol s)
    | RecordFieldMissing ({ ls_name = { id_string = s }} as cs,ls) ->
        Loc.error ?loc:(look_for_loc tdl s) (RecordFieldMissing (cs,ls))
    | DuplicateRecordField ({ ls_name = { id_string = s }} as cs,ls) ->
        Loc.error ?loc:(look_for_loc tdl s) (DuplicateRecordField (cs,ls))
    | DuplicateVar { vs_name = { id_string = s }} ->
        Loc.errorm ?loc:(look_for_loc tdl s)
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

let find_theory loc env mt path s = match path with
  | _::_ -> (* theory in file path *)
      Loc.try3 ~loc Env.read_theory env path s
  | [] -> (* local theory *)
      try Mstr.find s mt with Not_found ->
      Loc.try3 ~loc Env.read_theory env path s

let find_module loc env mm mt path s = match path with
  | _::_ -> (* module/theory in file path *)
      Loc.try3 ~loc read_module_or_theory env path s
  | [] -> (* local module/theory *)
      try Module (Mstr.find s mm) with Not_found ->
      try Theory (Mstr.find s mt) with Not_found ->
      Loc.try3 ~loc read_module_or_theory env path s

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
  | Ptree.Dtype tdl -> add_types ~wp uc tdl
  | decl -> add_decl loc uc decl

let add_decl ~wp loc uc d =
  if Debug.test_flag Typing.debug_parse_only then uc else
  Loc.try3 ~loc (add_decl ~wp) loc uc d

let add_pdecl ~wp _loc uc = function
  | Dfun (id, gh, lam) ->
      let id, gh = add_lemma_label ~top:true id gh in
      let bl, de, sp = dlambda (create_lenv uc) denv_empty lam in
      let fd = create_user_id id, gh, bl, de, sp in
      let uc = flush_tuples uc in
      let kn = get_known uc in
      let lkn = Theory.get_known (get_theory uc) in
      let fd = Mlw_dexpr.fun_defn ~keep_loc:true lkn kn fd in
      add_pdecl_with_tuples ~wp uc (create_rec_decl [fd])
  | Drec fdl ->
      let _, rd = drec_defn ~top:true (create_lenv uc) denv_empty fdl in
      let uc = flush_tuples uc in
      let kn = get_known uc in
      let lkn = Theory.get_known (get_theory uc) in
      let fdl = Mlw_dexpr.rec_defn ~keep_loc:true lkn kn rd in
      add_pdecl_with_tuples ~wp uc (create_rec_decl fdl)
  | Dval (id, gh, tyv) ->
      let id, gh = add_lemma_label ~top:true id gh in
      let tyv = dtype_v (create_lenv uc) tyv in
      let vd = create_user_id id, gh, tyv in
      let uc = flush_tuples uc in
      let kn = get_known uc in
      let lkn = Theory.get_known (get_theory uc) in
      let lv = Mlw_dexpr.val_decl ~keep_loc:true lkn kn vd in
      add_pdecl_with_tuples ~wp uc (create_val_decl lv)
  | Dexn (id, pty) ->
      let ity = ity_of_pty uc pty in
      let xs = create_xsymbol (create_user_id id) ity in
      add_pdecl_with_tuples ~wp uc (create_exn_decl xs)

let add_pdecl ~wp loc uc d =
  if Debug.test_flag Typing.debug_parse_only then uc else
  Loc.try3 ~loc (add_pdecl ~wp) loc uc d

let use_clone_pure env mth uc loc (use,inst) =
  let path, s = match use.use_theory with
    | Qdot (p,id) -> Typing.string_list_of_qualid p, id
    | Qident id -> [], id in
  let th = find_theory loc env mth path s.id_str in
  if Debug.test_flag Glob.flag then Glob.use s.id_loc th.th_name;
  (* open namespace, if any *)
  let uc = match use.use_import with
    | Some (_, use_as) -> Theory.open_namespace uc use_as
    | None -> uc in
  (* use or clone *)
  let uc = match inst with
    | None -> Theory.use_export uc th
    | Some inst ->
        Theory.warn_clone_not_abstract loc th;
        Theory.clone_export uc th (Typing.type_inst uc th inst) in
  (* close namespace, if any *)
  match use.use_import with
    | Some (import, _) -> Theory.close_namespace uc import
    | None -> uc

let use_clone_pure env mth uc loc use =
  if Debug.test_flag Typing.debug_parse_only then uc else
  Loc.try5 ~loc use_clone_pure env mth uc loc use

let use_clone env mmd mth uc loc (use,inst) =
  let path, s = match use.use_theory with
    | Qdot (p,id) -> Typing.string_list_of_qualid p, id
    | Qident id -> [], id in
  let mth = find_module loc env mmd mth path s.id_str in
  if Debug.test_flag Glob.flag then Glob.use s.id_loc
    (match mth with Module m -> m.mod_theory.th_name | Theory th -> th.th_name);
  (* open namespace, if any *)
  let uc = match use.use_import with
    | Some (_, use_as) -> open_namespace uc use_as
    | None -> uc in
  (* use or clone *)
  let uc = match mth, inst with
    | Module m, None -> use_export uc m
    | Theory th, None -> use_export_theory uc th
    | Module m, Some inst ->
        Theory.warn_clone_not_abstract loc m.mod_theory;
        let pure_inst, prog_inst = List.partition (function
          | CSvsym _ -> false | _ -> true) inst in
        let pure_sm = Typing.type_inst (get_theory uc) m.mod_theory pure_inst in
        let prog_sm = { inst_pv = Mpv.empty; inst_ps = Mps.empty } in
        let prog_sm = List.fold_left (fun s i -> match i with
          | CSvsym (loc,p,q) ->
              begin match ns_find_ps m.mod_export p, uc_find_ps uc q with
              | PV pv1, PV pv2 ->
                  if Mpv.mem pv1 s.inst_pv then Loc.error ~loc
                    (Theory.ClashSymbol pv1.pv_vs.vs_name.id_string);
                  { s with inst_pv = Mpv.add pv1 pv2 s.inst_pv }
              | PS ps1, PS ps2 ->
                  if Mps.mem ps1 s.inst_ps then Loc.error ~loc
                    (Theory.ClashSymbol ps1.ps_name.id_string);
                  { s with inst_ps = Mps.add ps1 ps2 s.inst_ps }
              | PV _, PS _ | PS _, PV _ -> Loc.errorm ~loc
                  "type mismatch"
              | PV _, _ | PS _, _ -> Loc.errorm ~loc
                  "not a program symbol: %a" print_qualid q
              | _ -> Loc.errorm ~loc
                  "not a program symbol: %a" print_qualid p
              end
          | _ -> assert false) prog_sm prog_inst in
        clone_export uc m prog_sm pure_sm
    | Theory th, Some inst ->
        Theory.warn_clone_not_abstract loc th;
        clone_export_theory uc th (Typing.type_inst (get_theory uc) th inst) in
  (* close namespace, if any *)
  match use.use_import with
    | Some (import, _) -> close_namespace uc import
    | None -> uc

let use_clone env mmd mth uc loc use =
  if Debug.test_flag Typing.debug_parse_only then uc else
  Loc.try6 ~loc use_clone env mmd mth uc loc use

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
  if Debug.test_flag Glob.flag then Glob.def m.mod_theory.th_name;
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
  let open_file env path =
    let wp = path = [] && Debug.test_noflag Typing.debug_type_only in
    Stack.push (Mstr.empty,Mstr.empty) lenv;
    let open_theory id = Stack.push false inm;
      Stack.push (Theory.create_theory ~path (Typing.create_user_id id)) tuc in
    let open_module id = Stack.push true inm;
      Stack.push (create_module env ~path (Typing.create_user_id id)) muc in
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
      then Stack.push (use_clone env mmd mth (Stack.pop muc) loc use) muc
      else Stack.push (use_clone_pure env mth (Stack.pop tuc) loc use) tuc in
    { open_theory = open_theory;
      close_theory = close_theory;
      open_module = open_module;
      close_module = close_module;
      open_namespace = open_namespace;
      close_namespace = (fun loc imp -> Loc.try1 ~loc close_namespace imp);
      new_decl = new_decl;
      new_pdecl = new_pdecl;
      use_clone = use_clone; }
  in
  let close_file () = Stack.pop lenv in
  open_file, close_file

(** Exception printing *)

let () = Exn_printer.register (fun fmt e -> match e with
  | DuplicateTypeVar s ->
      Format.fprintf fmt "Type parameter %s is used twice" s
  | UnboundTypeVar s ->
      Format.fprintf fmt "Unbound type variable '%s" s
  | _ -> raise e)
