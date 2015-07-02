(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2015   --   INRIA - CNRS - Paris-Sud University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)

open Stdlib
open Ident
open Ptree
open Ty
open Term
open Decl
open Theory
open Dterm
open Ity
open Expr
open Pdecl
open Pmodule

(** debug flags *)

let debug_parse_only = Debug.register_flag "parse_only"
  ~desc:"Stop@ after@ parsing."

let debug_type_only  = Debug.register_flag "type_only"
  ~desc:"Stop@ after@ type-checking."

(** symbol lookup *)

let rec qloc = function
  | Qdot (p, id) -> Loc.join (qloc p) id.id_loc
  | Qident id    -> id.id_loc

let qloc_last = function
  | Qdot (_, id) | Qident id -> id.id_loc

let rec print_qualid fmt = function
  | Qdot (p, id) -> Format.fprintf fmt "%a.%s" print_qualid p id.id_str
  | Qident id    -> Format.fprintf fmt "%s" id.id_str

let string_list_of_qualid q =
  let rec sloq acc = function
    | Qdot (p, id) -> sloq (id.id_str :: acc) p
    | Qident id -> id.id_str :: acc in
  sloq [] q

exception UnboundSymbol of qualid

let find_qualid get_id find ns q =
  let sl = string_list_of_qualid q in
  let r = try find ns sl with Not_found ->
    Loc.error ~loc:(qloc q) (UnboundSymbol q) in
  if Debug.test_flag Glob.flag then Glob.use (qloc_last q) (get_id r);
  r

let find_prop_ns     ns q = find_qualid (fun pr -> pr.pr_name) ns_find_pr ns q
let find_tysymbol_ns ns q = find_qualid (fun ts -> ts.ts_name) ns_find_ts ns q
let find_lsymbol_ns  ns q = find_qualid (fun ls -> ls.ls_name) ns_find_ls ns q

let find_fsymbol_ns ns q =
  let ls = find_lsymbol_ns ns q in
  if ls.ls_value <> None then ls else
    Loc.error ~loc:(qloc q) (FunctionSymbolExpected ls)

let find_psymbol_ns ns q =
  let ls = find_lsymbol_ns ns q in
  if ls.ls_value = None then ls else
    Loc.error ~loc:(qloc q) (PredicateSymbolExpected ls)

let find_tysymbol tuc q = find_tysymbol_ns (Theory.get_namespace tuc) q
let find_lsymbol  tuc q = find_lsymbol_ns  (Theory.get_namespace tuc) q
let find_fsymbol  tuc q = find_fsymbol_ns  (Theory.get_namespace tuc) q
let find_psymbol  tuc q = find_psymbol_ns  (Theory.get_namespace tuc) q
let find_prop     tuc q = find_prop_ns     (Theory.get_namespace tuc) q

let find_prop_of_kind k tuc q =
  let pr = find_prop tuc q in
  match (Mid.find pr.pr_name (Theory.get_known tuc)).d_node with
  | Dprop (l,_,_) when l = k -> pr
  | _ -> Loc.errorm ~loc:(qloc q) "proposition %a is not %s"
      print_qualid q (match k with
        | Plemma -> "a lemma" | Paxiom -> "an axiom"
        | Pgoal  -> "a goal"  | Pskip  -> assert false (* what? *))

let find_itysymbol_ns ns q =
  find_qualid (fun s -> s.its_ts.ts_name) Pmodule.ns_find_its ns q

let find_xsymbol_ns ns q =
  find_qualid (fun s -> s.xs_name) Pmodule.ns_find_xs ns q

let find_prog_symbol_ns ns p =
  let get_id_ps = function
    | PV pv -> pv.pv_vs.vs_name
    | RS rs -> rs.rs_name in
  find_qualid get_id_ps ns_find_prog_symbol ns p

let get_namespace muc = List.hd muc.Pmodule.muc_import

let find_xsymbol     muc q = find_xsymbol_ns     (get_namespace muc) q
let find_itysymbol   muc q = find_itysymbol_ns   (get_namespace muc) q
let find_prog_symbol muc q = find_prog_symbol_ns (get_namespace muc) q

let find_rsymbol muc q = match find_prog_symbol muc q with RS rs -> rs
  | _ -> Loc.errorm ~loc:(qloc q) "program symbol expected"

(** Parsing types *)

let ty_of_pty tuc pty =
  let rec get_ty = function
    | PTtyvar {id_str = x} ->
        ty_var (tv_of_string x)
    | PTtyapp (q, tyl) ->
        let s = find_tysymbol tuc q in
        let tyl = List.map get_ty tyl in
        Loc.try2 ~loc:(qloc q) ty_app s tyl
    | PTtuple tyl ->
        let s = its_tuple (List.length tyl) in
        ty_app s.its_ts (List.map get_ty tyl)
    | PTarrow (ty1, ty2) ->
        ty_func (get_ty ty1) (get_ty ty2)
    | PTparen ty ->
        get_ty ty
  in
  get_ty pty

let ity_of_pty muc pty =
  let rec get_ity = function
    | PTtyvar {id_str = x} ->
        ity_var (tv_of_string x)
    | PTtyapp (q, tyl) ->
        let s = find_itysymbol muc q in
        let tyl = List.map get_ity tyl in
        Loc.try2 ~loc:(qloc q) ity_app_fresh s tyl
    | PTtuple tyl ->
        ity_tuple (List.map get_ity tyl)
    | PTarrow (ty1, ty2) ->
        ity_func (get_ity ty1) (get_ity ty2)
    | PTparen ty ->
        get_ity ty
  in
  get_ity pty

(** typing using destructive type variables

    parsed trees        intermediate trees       typed trees
      (Ptree)                (Dterm)               (Term)
   -----------------------------------------------------------
     ppure_type  ---dty--->   dty       ---ty--->    ty
      lexpr      --dterm-->   dterm     --term-->    term
*)

(** Typing patterns, terms, and formulas *)

let create_user_id {id_str = n; id_lab = label; id_loc = loc} =
  let get_labels (label, loc) = function
    | Lstr lab -> Slab.add lab label, loc | Lpos loc -> label, loc in
  let label,loc = List.fold_left get_labels (Slab.empty,loc) label in
  id_user ~label n loc

let parse_record ~loc tuc get_val fl =
  let fl = List.map (fun (q,e) -> find_lsymbol tuc q, e) fl in
  let cs,pjl,flm = Loc.try2 ~loc parse_record (get_known tuc) fl in
  let get_val pj = get_val cs pj (Mls.find_opt pj flm) in
  cs, List.map get_val pjl

let rec dpattern tuc { pat_desc = desc; pat_loc = loc } =
  Dterm.dpattern ~loc (match desc with
    | Ptree.Pwild -> DPwild
    | Ptree.Pvar x -> DPvar (create_user_id x)
    | Ptree.Papp (q,pl) ->
        let pl = List.map (dpattern tuc) pl in
        DPapp (find_lsymbol tuc q, pl)
    | Ptree.Ptuple pl ->
        let pl = List.map (dpattern tuc) pl in
        DPapp (fs_tuple (List.length pl), pl)
    | Ptree.Prec fl ->
        let get_val _ _ = function
          | Some p -> dpattern tuc p
          | None -> Dterm.dpattern DPwild in
        let cs,fl = parse_record ~loc tuc get_val fl in
        DPapp (cs,fl)
    | Ptree.Pas (p, x) -> DPas (dpattern tuc p, create_user_id x)
    | Ptree.Por (p, q) -> DPor (dpattern tuc p, dpattern tuc q)
    | Ptree.Pcast (p, ty) -> DPcast (dpattern tuc p, ty_of_pty tuc ty))

let quant_var tuc (loc, id, gh, ty) =
  assert (not gh);
  let ty = match ty with
    | Some ty -> dty_of_ty (ty_of_pty tuc ty)
    | None    -> dty_fresh () in
  Opt.map create_user_id id, ty, Some loc

let is_reusable dt = match dt.dt_node with
  | DTvar _ | DTgvar _ | DTconst _ | DTtrue | DTfalse -> true
  | DTapp (_,[]) -> true
  | _ -> false

let mk_var n dt =
  let dty = match dt.dt_dty with
    | None -> dty_of_ty ty_bool
    | Some dty -> dty in
  Dterm.dterm ?loc:dt.dt_loc (DTvar (n, dty))

let mk_let ~loc n dt node =
  DTlet (dt, id_user n loc, Dterm.dterm ~loc node)

let chainable_op tuc op =
  (* non-bool -> non-bool -> bool *)
  op.id_str = "infix =" || op.id_str = "infix <>" ||
  match find_lsymbol tuc (Qident op) with
  | {ls_args = [ty1;ty2]; ls_value = ty} ->
      Opt.fold (fun _ ty -> ty_equal ty ty_bool) true ty
      && not (ty_equal ty1 ty_bool)
      && not (ty_equal ty2 ty_bool)
  | _ -> false

let mk_closure loc ls =
  let mk dt = Dterm.dterm ~loc dt in
  let mk_v i _ =
    Some (id_user ("y" ^ string_of_int i) loc), dty_fresh (), None in
  let mk_t (id, dty, _) = mk (DTvar ((Opt.get id).pre_name, dty)) in
  let vl = Lists.mapi mk_v ls.ls_args in
  DTquant (DTlambda, vl, [], mk (DTapp (ls, List.map mk_t vl)))

let rec dterm tuc gvars at denv {term_desc = desc; term_loc = loc} =
  let func_app e el =
    List.fold_left (fun e1 (loc, e2) ->
      DTfapp (Dterm.dterm ~loc e1, e2)) e el
  in
  let rec apply_ls loc ls al l el = match l, el with
    | (_::l), (e::el) -> apply_ls loc ls (e::al) l el
    | [], _ -> func_app (DTapp (ls, List.rev_map snd al)) el
    | _, [] -> func_app (mk_closure loc ls) (List.rev_append al el)
  in
  let qualid_app q el = match gvars at q with
    | Some v -> func_app (DTgvar v.pv_vs) el
    | None ->
        let ls = find_lsymbol tuc q in
        apply_ls (qloc q) ls [] ls.ls_args el
  in
  let qualid_app q el = match q with
    | Qident {id_str = n} ->
        (match denv_get_opt denv n with
        | Some d -> func_app d el
        | None -> qualid_app q el)
    | _ -> qualid_app q el
  in
  let rec unfold_app e1 e2 el = match e1.term_desc with
    | Ptree.Tapply (e11,e12) ->
        let e12 = dterm tuc gvars at denv e12 in
        unfold_app e11 e12 ((e1.term_loc, e2)::el)
    | Ptree.Tident q ->
        qualid_app q ((e1.term_loc, e2)::el)
    | _ ->
        func_app (DTfapp (dterm tuc gvars at denv e1, e2)) el
  in
  Dterm.dterm ~loc (match desc with
  | Ptree.Tident q ->
      qualid_app q []
  | Ptree.Tidapp (q, tl) ->
      let tl = List.map (dterm tuc gvars at denv) tl in
      DTapp (find_lsymbol tuc q, tl)
  | Ptree.Tapply (e1, e2) ->
      unfold_app e1 (dterm tuc gvars at denv e2) []
  | Ptree.Ttuple tl ->
      let tl = List.map (dterm tuc gvars at denv) tl in
      DTapp (fs_tuple (List.length tl), tl)
  | Ptree.Tinfix (e12, op2, e3)
  | Ptree.Tinnfix (e12, op2, e3) ->
      let make_app de1 op de2 = if op.id_str = "infix <>" then
        let op = { op with id_str = "infix =" } in
        let ls = find_lsymbol tuc (Qident op) in
        DTnot (Dterm.dterm ~loc (DTapp (ls, [de1;de2])))
      else
        DTapp (find_lsymbol tuc (Qident op), [de1;de2])
      in
      let rec make_chain de1 = function
        | [op,de2] ->
            make_app de1 op de2
        | (op,de2) :: ch ->
            let de12 = Dterm.dterm ~loc (make_app de1 op de2) in
            let de23 = Dterm.dterm ~loc (make_chain de2 ch) in
            DTbinop (DTand, de12, de23)
        | [] -> assert false in
      let rec get_chain e12 acc = match e12.term_desc with
        | Tinfix (e1, op1, e2) when chainable_op tuc op1 ->
            get_chain e1 ((op1, dterm tuc gvars at denv e2) :: acc)
        | _ -> e12, acc in
      let ch = [op2, dterm tuc gvars at denv e3] in
      let e1, ch = if chainable_op tuc op2
        then get_chain e12 ch else e12, ch in
      make_chain (dterm tuc gvars at denv e1) ch
  | Ptree.Tconst c ->
      DTconst c
  | Ptree.Tlet (x, e1, e2) ->
      let id = create_user_id x in
      let e1 = dterm tuc gvars at denv e1 in
      let denv = denv_add_let denv e1 id in
      let e2 = dterm tuc gvars at denv e2 in
      DTlet (e1, id, e2)
  | Ptree.Tmatch (e1, bl) ->
      let e1 = dterm tuc gvars at denv e1 in
      let branch (p, e) =
        let p = dpattern tuc p in
        let denv = denv_add_pat denv p in
        p, dterm tuc gvars at denv e in
      DTcase (e1, List.map branch bl)
  | Ptree.Tif (e1, e2, e3) ->
      let e1 = dterm tuc gvars at denv e1 in
      let e2 = dterm tuc gvars at denv e2 in
      let e3 = dterm tuc gvars at denv e3 in
      DTif (e1, e2, e3)
  | Ptree.Ttrue ->
      DTtrue
  | Ptree.Tfalse ->
      DTfalse
  | Ptree.Tunop (Ptree.Tnot, e1) ->
      DTnot (dterm tuc gvars at denv e1)
  | Ptree.Tbinop (e1, op, e2) ->
      let e1 = dterm tuc gvars at denv e1 in
      let e2 = dterm tuc gvars at denv e2 in
      let op = match op with
        | Ptree.Tand -> DTand
        | Ptree.Tand_asym -> DTand_asym
        | Ptree.Tor -> DTor
        | Ptree.Tor_asym -> DTor_asym
        | Ptree.Timplies -> DTimplies
        | Ptree.Tiff -> DTiff in
      DTbinop (op, e1, e2)
  | Ptree.Tquant (q, uqu, trl, e1) ->
      let qvl = List.map (quant_var tuc) uqu in
      let denv = denv_add_quant denv qvl in
      let dterm e = dterm tuc gvars at denv e in
      let trl = List.map (List.map dterm) trl in
      let e1 = dterm e1 in
      let q = match q with
        | Ptree.Tforall -> DTforall
        | Ptree.Texists -> DTexists
        | Ptree.Tlambda -> DTlambda in
      DTquant (q, qvl, trl, e1)
  | Ptree.Trecord fl ->
      let get_val cs pj = function
        | Some e -> dterm tuc gvars at denv e
        | None -> Loc.error ~loc (RecordFieldMissing (cs,pj)) in
      let cs, fl = parse_record ~loc tuc get_val fl in
      DTapp (cs, fl)
  | Ptree.Tupdate (e1, fl) ->
      let e1 = dterm tuc gvars at denv e1 in
      let re = is_reusable e1 in
      let v = if re then e1 else mk_var "_q " e1 in
      let get_val _ pj = function
        | Some e -> dterm tuc gvars at denv e
        | None -> Dterm.dterm ~loc (DTapp (pj,[v])) in
      let cs, fl = parse_record ~loc tuc get_val fl in
      let d = DTapp (cs, fl) in
      if re then d else mk_let ~loc "_q " e1 d
  | Ptree.Tat (e1, l) ->
      DTlabel (dterm tuc gvars (Some l.id_str) denv e1, Slab.empty)
  | Ptree.Tnamed (Lpos uloc, e1) ->
      DTuloc (dterm tuc gvars at denv e1, uloc)
  | Ptree.Tnamed (Lstr lab, e1) ->
      DTlabel (dterm tuc gvars at denv e1, Slab.singleton lab)
  | Ptree.Tcast (e1, ty) ->
      DTcast (dterm tuc gvars at denv e1, ty_of_pty tuc ty))

(** typing program expressions *)

open Dexpr

(* records *)

let find_record_field muc q =
  match find_prog_symbol muc q with RS ({rs_field = Some _} as s) -> s
  | _ -> Loc.errorm ~loc:(qloc q) "Not a record field: %a" print_qualid q

let find_record_field2 muc (q,e) = find_record_field muc q, e

let parse_record muc fll =
  (* we assume that every rsymbol in fll was resolved
     using find_record_field, so they are all fields *)
  let ls_of_rs rs = match rs.rs_logic with
    | RLls ls -> ls | _ -> assert false in
  let rs = match fll with
    | (rs, _)::_ -> rs
    | [] -> raise EmptyRecord in
  let its = match rs.rs_cty.cty_args with
    | [{pv_ity = {ity_node = (Ityreg {reg_its = its}
        | Ityapp (its,_,_) | Itypur (its,_))}}] -> its
    | _ -> raise (BadRecordField (ls_of_rs rs)) in
  let itd = find_its_defn muc.muc_known its in
  let check v s = match s.rs_field with
    | Some u -> pv_equal v u
    | _ -> false in
  let cs = match itd.itd_constructors with
    | [cs] when Lists.equal check cs.rs_cty.cty_args itd.itd_fields -> cs
    | _ -> raise (BadRecordField (ls_of_rs rs)) in
  let pjs = Srs.of_list itd.itd_fields in
  let flm = List.fold_left (fun m (pj,v) -> if Srs.mem pj pjs then
    Mrs.add_new (DuplicateRecordField (ls_of_rs cs, ls_of_rs pj)) pj v m
    else raise (BadRecordField (ls_of_rs pj))) Mrs.empty fll in
  cs, itd.itd_fields, flm

let parse_record ~loc muc get_val fl =
  let fl = List.map (find_record_field2 muc) fl in
  let cs,pjl,flm = Loc.try2 ~loc parse_record muc fl in
  let get_val pj = get_val cs pj (Mrs.find_opt pj flm) in
  cs, List.map get_val pjl

(* patterns *)

let rec dpattern muc { pat_desc = desc; pat_loc = loc } =
  Dexpr.dpattern ~loc (match desc with
    | Ptree.Pwild -> DPwild
    | Ptree.Pvar x -> DPvar (create_user_id x)
    | Ptree.Papp (q,pl) ->
        DPapp (find_rsymbol muc q, List.map (fun p -> dpattern muc p) pl)
    | Ptree.Prec fl ->
        let get_val _ _ = function
          | Some p -> dpattern muc p
          | None -> Dexpr.dpattern DPwild in
        let cs,fl = parse_record ~loc muc get_val fl in
        DPapp (cs,fl)
    | Ptree.Ptuple pl ->
        DPapp (rs_tuple (List.length pl), List.map (dpattern muc) pl)
    | Ptree.Pcast (p, pty) -> DPcast (dpattern muc p, ity_of_pty muc pty)
    | Ptree.Pas (p, x) -> DPas (dpattern muc p, create_user_id x)
    | Ptree.Por (p, q) -> DPor (dpattern muc p, dpattern muc q))

(* specifications *)

let find_global_pv muc q = try match find_prog_symbol muc q with
  | PV v -> Some v | _ -> None with _ -> None

let find_local_pv muc lvm q = match q with
  | Qdot _ -> find_global_pv muc q
  | Qident id -> let ovs = Mstr.find_opt id.id_str lvm in
      if ovs = None then find_global_pv muc q else ovs

let mk_gvars muc lvm old = fun at q ->
  match find_local_pv muc lvm q, at with
  | Some v, Some l -> Some (old v l)
  | v, _ -> v

let type_term muc lvm old t =
  let gvars = mk_gvars muc lvm old in
  let t = dterm muc.muc_theory gvars None Dterm.denv_empty t in
  Dterm.term ~strict:true ~keep_loc:true t

let type_fmla muc lvm old f =
  let gvars = mk_gvars muc lvm old in
  let f = dterm muc.muc_theory gvars None Dterm.denv_empty f in
  Dterm.fmla ~strict:true ~keep_loc:true f

let dpre muc pl lvm old =
  let dpre f = type_fmla muc lvm old f in
  List.map dpre pl

let dpost muc ql lvm old ity =
  let dpost (loc,pfl) = match pfl with
    | [{ pat_desc = Ptree.Pwild | Ptree.Ptuple [] }, f] ->
        let v = create_pvsymbol (id_fresh "result") ity in
        v, Loc.try3 ~loc type_fmla muc lvm old f
    | [{ pat_desc = Ptree.Pvar id }, f] ->
        let v = create_pvsymbol (create_user_id id) ity in
        let lvm = Mstr.add id.id_str v lvm in
        v, Loc.try3 ~loc type_fmla muc lvm old f
    | _ ->
        let v = create_pvsymbol (id_fresh "result") ity in
        let i = { id_str = "(null)"; id_loc = loc; id_lab = [] } in
        let t = { term_desc = Tident (Qident i); term_loc = loc } in
        let f = { term_desc = Tmatch (t, pfl); term_loc = loc } in
        let lvm = Mstr.add "(null)" v lvm in
        v, Loc.try3 ~loc type_fmla muc lvm old f in
  List.map dpost ql

let dxpost muc ql lvm old =
  let add_exn (q,pat,f) m =
    let xs = find_xsymbol muc q in
    Mexn.change (function
      | Some l -> Some ((pat,f) :: l)
      | None   -> Some ((pat,f) :: [])) xs m in
  let mk_xpost loc xs pfl =
    dpost muc [loc,pfl] lvm old xs.xs_ity in
  let exn_map (loc,xpfl) =
    let m = List.fold_right add_exn xpfl Mexn.empty in
    Mexn.mapi (fun xs pfl -> mk_xpost loc xs pfl) m in
  let add_map ql m =
    Mexn.union (fun _ l r -> Some (l @ r)) (exn_map ql) m in
  List.fold_right add_map ql Mexn.empty

let dreads muc rl lvm =
  let dreads q = match find_local_pv muc lvm q with Some v -> v
    | None -> Loc.errorm ~loc:(qloc q) "Not a variable: %a" print_qualid q in
  List.map dreads rl

let dwrites muc wl lvm =
  let old _ _ = Loc.errorm
    "`at' and `old' cannot be used in the `writes' clause" in
  let dwrites t = type_term muc lvm old t in
  List.map dwrites wl

let find_variant_ls muc q = match find_lsymbol muc.muc_theory q with
  | { ls_args = [u;v]; ls_value = None } as ls when ty_equal u v -> ls
  | s -> Loc.errorm ~loc:(qloc q) "Not an order relation: %a" Pretty.print_ls s

let dvariant muc varl lvm old =
  let dvar t = type_term muc lvm old t in
  let dvar (t,q) = dvar t, Opt.map (find_variant_ls muc) q in
  List.map dvar varl

let dspec muc sp lvm old ity = {
  ds_pre     = dpre muc sp.sp_pre lvm old;
  ds_post    = dpost muc sp.sp_post lvm old ity;
  ds_xpost   = dxpost muc sp.sp_xpost lvm old;
  ds_reads   = dreads muc sp.sp_reads lvm;
  ds_writes  = dwrites muc sp.sp_writes lvm;
  ds_checkrw = sp.sp_checkrw;
  ds_diverge = sp.sp_diverge; }

let dassert muc f lvm old = type_fmla muc lvm old f

let dinvariant muc f lvm old = dpre muc f lvm old

(* abstract values *)

let dbinder muc id gh pty =
  let id = Opt.map create_user_id id in
  let dity = match pty with
    | Some pty -> dity_of_ity (ity_of_pty muc pty)
    | None -> dity_fresh () in
  id, gh, dity

let dparam muc (_,id,gh,pty) = dbinder muc id gh (Some pty)

let dbinder muc (_,id,gh,pty) = dbinder muc id gh pty

(* expressions *)

let is_reusable de = match de.de_node with
  | DEvar _ | DEpv _ | DEconst _ | DEtrue | DEfalse -> true
  | DErs {rs_logic = (RLls _|RLpv _); rs_cty = cty} ->
      cty.cty_args = [] && cty.cty_result.ity_pure
  | _ -> false

let mk_var n de =
  Dexpr.dexpr ?loc:de.de_loc (DEvar (n, de.de_dvty))

let mk_let ~loc n de node =
  let de1 = Dexpr.dexpr ~loc node in
  DElet ((id_user n loc, false, RKnone, de), de1)

let chainable_rs = function
  | {rs_cty = { cty_args = [pv1;pv2]; cty_result = ity}} ->
      ity_equal ity ity_bool
      && not (ity_equal pv1.pv_ity ity_bool)
      && not (ity_equal pv2.pv_ity ity_bool)
  | _ -> false

let chainable_qualid muc p = match find_prog_symbol muc p with
  | RS s -> chainable_rs s
  | _ -> false

let chainable_op muc denv op =
  (* non-bool -> non-bool -> bool *)
  op.id_str = "infix =" || op.id_str = "infix <>" ||
  match denv_get_opt denv op.id_str with
  | Some (DEvar (_,t)) -> dvty_is_chainable t
  | Some (DErs s) -> chainable_rs s
  | Some _ -> false (* can never happen *)
  | None -> chainable_qualid muc (Qident op)

let rec dexpr muc denv {expr_desc = desc; expr_loc = loc} =
  let expr_app loc e el =
    List.fold_left (fun e1 e2 ->
      DEapp (Dexpr.dexpr ~loc e1, e2)) e el
  in
  let qualid_app loc q el = match find_prog_symbol muc q with
    | PV pv -> expr_app loc (DEpv pv) el
    | RS rs -> expr_app loc (DErs rs) el
  in
  let qualid_app loc q el = match q with
    | Qident {id_str = n} ->
        (match denv_get_opt denv n with
        | Some d -> expr_app loc d el
        | None -> qualid_app loc q el)
    | _ -> qualid_app loc q el
  in
  Dexpr.dexpr ~loc (match desc with
  | Ptree.Eident q ->
      qualid_app loc q []
  | Ptree.Eidapp (q, el) ->
      qualid_app loc q (List.map (dexpr muc denv) el)
  | Ptree.Eapply (e1, e2) ->
      DEapp (dexpr muc denv e1, dexpr muc denv e2)
  | Ptree.Etuple el ->
      let e = DErs (rs_tuple (List.length el)) in
      expr_app loc e (List.map (dexpr muc denv) el)
  | Ptree.Einfix (e12, op2, e3)
  | Ptree.Einnfix (e12, op2, e3) ->
      let make_app de1 op de2 = if op.id_str = "infix <>" then
        let oq = Qident { op with id_str = "infix =" } in
        let dt = qualid_app op.id_loc oq [de1; de2] in
        DEnot (Dexpr.dexpr ~loc dt)
      else
        qualid_app op.id_loc (Qident op) [de1; de2]
      in
      let rec make_chain n1 n2 de1 = function
        | [op,de2] ->
            make_app de1 op de2
        | (op,de2) :: ch ->
            let re = is_reusable de2 in
            let v = if re then de2 else mk_var n1 de2 in
            let de12 = Dexpr.dexpr ~loc (make_app de1 op v) in
            let de23 = Dexpr.dexpr ~loc (make_chain n2 n1 v ch) in
            let d = DEand (de12, de23) in
            if re then d else mk_let ~loc n1 de2 d
        | [] -> assert false in
      let rec get_chain e12 acc = match e12.expr_desc with
        | Ptree.Einfix (e1, op1, e2) when chainable_op muc denv op1 ->
            get_chain e1 ((op1, dexpr muc denv e2) :: acc)
        | _ -> e12, acc in
      let ch = [op2, dexpr muc denv e3] in
      let e1, ch = if chainable_op muc denv op2
        then get_chain e12 ch else e12, ch in
      make_chain "q1 " "q2 " (dexpr muc denv e1) ch
  | Ptree.Econst c -> DEconst c
  | Ptree.Erecord fl ->
      let ls_of_rs rs = match rs.rs_logic with
        | RLls ls -> ls | _ -> assert false in
      let get_val cs pj = function
        | None -> Loc.error ~loc
            (Decl.RecordFieldMissing (ls_of_rs cs, ls_of_rs pj))
        | Some e -> dexpr muc denv e in
      let cs,fl = parse_record ~loc muc get_val fl in
      expr_app loc (DErs cs) fl
  | Ptree.Eupdate (e1, fl) ->
      let e1 = dexpr muc denv e1 in
      let re = is_reusable e1 in
      let v = if re then e1 else mk_var "_q " e1 in
      let get_val _ pj = function
        | None ->
            let pj = Dexpr.dexpr ~loc (DErs pj) in
            Dexpr.dexpr ~loc (DEapp (pj, v))
        | Some e -> dexpr muc denv e in
      let cs,fl = parse_record ~loc muc get_val fl in
      let d = expr_app loc (DErs cs) fl in
      if re then d else mk_let ~loc "_q " e1 d
  | Ptree.Elet (id, gh, kind, e1, e2) ->
      let ld = create_user_id id, gh, kind, dexpr muc denv e1 in
      DElet (ld, dexpr muc (denv_add_let denv ld) e2)
  | Ptree.Erec (fdl, e1) ->
      let denv, rd = drec_defn muc denv fdl in
      DErec (rd, dexpr muc denv e1)
  | Ptree.Efun (bl, pty, sp, e) ->
      let bl = List.map (dbinder muc) bl in
      let e = match pty with
        | Some pty -> { e with expr_desc = Ecast (e, pty) }
        | None -> e in
      let ds = match sp.sp_variant with
        | ({term_loc = loc},_)::_ ->
            Loc.errorm ~loc "unexpected 'variant' clause"
        | _ -> dspec muc sp in
      DEfun (bl, ds, dexpr muc (denv_add_args denv bl) e)
  | Ptree.Eany (pl, pty, sp) ->
      let pl = List.map (dparam muc) pl in
      let ds = match sp.sp_variant with
        | ({term_loc = loc},_)::_ ->
            Loc.errorm ~loc "unexpected 'variant' clause"
        | _ -> dspec muc sp in
      DEany (pl, ds, dity_of_ity (ity_of_pty muc pty))
  | Ptree.Ematch (e1, bl) ->
      let e1 = dexpr muc denv e1 in
      let branch (pp, e) =
        let pp = dpattern muc pp in
        let denv = denv_add_pat denv pp in
        pp, dexpr muc denv e in
      DEcase (e1, List.map branch bl)
  | Ptree.Eif (e1, e2, e3) ->
      let e1 = dexpr muc denv e1 in
      let e2 = dexpr muc denv e2 in
      let e3 = dexpr muc denv e3 in
      DEif (e1, e2, e3)
  | Ptree.Enot e1 ->
      DEnot (dexpr muc denv e1)
  | Ptree.Eand (e1, e2) ->
      DEand (dexpr muc denv e1, dexpr muc denv e2)
  | Ptree.Eor (e1, e2) ->
      DEor (dexpr muc denv e1, dexpr muc denv e2)
  | Ptree.Etrue -> DEtrue
  | Ptree.Efalse -> DEfalse
  | Ptree.Esequence (e1, e2) ->
      let e1 = dexpr muc denv e1 in
      let e2 = dexpr muc denv e2 in
      DElet ((id_user "_" loc, false, RKnone, e1), e2)
  | Ptree.Ewhile (e1, inv, var, e2) ->
      let e1 = dexpr muc denv e1 in
      let e2 = dexpr muc denv e2 in
      let inv = dinvariant muc inv in
      let var = dvariant muc var in
      DEwhile (e1, inv, var, e2)
  | Ptree.Efor (id, efrom, dir, eto, inv, e1) ->
      let efrom = dexpr muc denv efrom in
      let eto = dexpr muc denv eto in
      let inv = dinvariant muc inv in
      let id = create_user_id id in
      let denv = denv_add_var denv id (dity_of_ity ity_int) in
      DEfor (id, efrom, dir, eto, inv, dexpr muc denv e1)
  | Ptree.Eassign (e1, q, e2) ->
      DEassign [dexpr muc denv e1, find_record_field muc q, dexpr muc denv e2]
  | Ptree.Eraise (q, e1) ->
      let xs = find_xsymbol muc q in
      let e1 = match e1 with
        | Some e1 -> dexpr muc denv e1
        | None when ity_equal xs.xs_ity ity_unit ->
            Dexpr.dexpr ~loc (DErs rs_void)
        | _ -> Loc.errorm ~loc "exception argument expected" in
      DEraise (xs, e1)
  | Ptree.Etry (e1, cl) ->
      let e1 = dexpr muc denv e1 in
      let branch (q, pp, e) =
        let xs = find_xsymbol muc q in
        let pp = match pp with
          | Some pp -> dpattern muc pp
          | None when ity_equal xs.xs_ity ity_unit ->
              Dexpr.dpattern ~loc (DPapp (rs_void, []))
          | _ -> Loc.errorm ~loc "exception argument expected" in
        let denv = denv_add_pat denv pp in
        let e = dexpr muc denv e in
        xs, pp, e in
      DEtry (e1, List.map branch cl)
  | Ptree.Eghost e1 ->
      DEghost (dexpr muc denv e1)
  | Ptree.Eabsurd -> DEabsurd
  | Ptree.Eassert (ak, lexpr) ->
      DEassert (ak, dassert muc lexpr)
  | Ptree.Emark (id, e1) ->
      DEmark (create_user_id id, dexpr muc denv e1)
  | Ptree.Enamed (Lpos uloc, e1) ->
      DEuloc (dexpr muc denv e1, uloc)
  | Ptree.Enamed (Lstr lab, e1) ->
      DElabel (dexpr muc denv e1, Slab.singleton lab)
  | Ptree.Ecast (e1, pty) ->
      DEcast (dexpr muc denv e1, ity_of_pty muc pty))

and drec_defn muc denv fdl =
  let prep (id, gh, kind, bl, pty, sp, e) =
    let bl = List.map (dbinder muc) bl in
    let dity = match pty with
      | Some pty -> dity_of_ity (ity_of_pty muc pty)
      | None -> dity_fresh () in
    let pre denv =
      let dv = dvariant muc sp.sp_variant in
      dspec muc sp, dv, dexpr muc denv e in
    create_user_id id, gh, kind, bl, dity, pre in
  Dexpr.drec_defn denv (List.map prep fdl)

(** Typing declarations *)

open Pdecl
open Pmodule

let add_pdecl ~vc muc d =
  if Debug.test_flag Glob.flag then Sid.iter Glob.def d.pd_news;
  add_pdecl ~vc muc d

let add_decl muc d = add_pdecl ~vc:false muc (create_pure_decl d)

let type_pure muc lvm denv e =
  let gvars at q = match at, q with
    | Some _, _ -> Loc.errorm ~loc:(qloc q)
        "`at' and `old' can only be used in program annotations"
    | None, Qident x -> Mstr.find_opt x.id_str lvm
    | None, Qdot _ -> None in
  dterm muc.muc_theory gvars None denv e

let type_term_pure muc lvm denv e =
  Dterm.term ~strict:true ~keep_loc:true (type_pure muc lvm denv e)

let type_fmla_pure muc lvm denv e =
  Dterm.fmla ~strict:true ~keep_loc:true (type_pure muc lvm denv e)

let add_types muc tdl =
  let add m ({td_ident = {id_str = x}; td_loc = loc} as d) =
    Mstr.add_new (Loc.Located (loc, ClashSymbol x)) x d m in
  let def = List.fold_left add Mstr.empty tdl in
  let hts = Hstr.create 5 in
  let htd = Hstr.create 5 in
  let rec visit ~alias ~alg x d = if not (Hstr.mem htd x) then
    let id = create_user_id d.td_ident and loc = d.td_loc in
    let args = List.map (fun id -> tv_of_string id.id_str) d.td_params in
    match d.td_def with
    | TDabstract ->
        if d.td_inv <> [] then Loc.errorm ~loc
          "Abstract non-record types cannot have invariants";
        let itd = create_abstract_type_decl id args d.td_mut in
        Hstr.add hts x itd.itd_its; Hstr.add htd x itd
    | TDalias pty ->
        if d.td_vis <> Public || d.td_mut then Loc.errorm ~loc
          "Alias types cannot be abstract, private. or mutable";
        if d.td_inv <> [] then Loc.errorm ~loc
          "Alias types cannot have invariants";
        let alias = Sstr.add x alias in
        let ity = parse ~loc ~alias ~alg pty in
        if not (Hstr.mem htd x) then
        let itd = create_alias_decl id args ity in
        Hstr.add hts x itd.itd_its; Hstr.add htd x itd
    | TDalgebraic csl ->
        if d.td_vis <> Public || d.td_mut then Loc.errorm ~loc
          "Algebraic types cannot be abstract, private. or mutable";
        if d.td_inv <> [] then Loc.errorm ~loc
          "Algebraic types cannot have invariants";
        let hfd = Hstr.create 5 in
        let alias = Sstr.empty in
        let alg = Mstr.add x (id,args) alg in
        let get_pj nms (_, id, ghost, pty) = match id with
          | Some ({id_str = nm} as id) ->
              let exn = Loc.Located (id.id_loc, Loc.Message ("Field " ^
                nm ^ " is used more than once in the same constructor")) in
              let nms = Sstr.add_new exn nm nms in
              let ity = parse ~loc ~alias ~alg pty in
              let v = try Hstr.find hfd nm with Not_found ->
                let v = create_pvsymbol (create_user_id id) ~ghost ity in
                Hstr.add hfd nm v;
                v in
              if not (ity_equal v.pv_ity ity && ghost = v.pv_ghost) then
                Loc.errorm ~loc "Conflicting definitions for field %s" nm;
              nms, (true, v)
          | None ->
              let ity = parse ~loc ~alias ~alg pty in
              nms, (false, create_pvsymbol (id_fresh "a") ~ghost ity) in
        let get_cs oms (_, id, pjl) =
          let nms, pjl = Lists.map_fold_left get_pj Sstr.empty pjl in
          if Sstr.equal oms nms then create_user_id id, pjl else
            let df = Sstr.union (Sstr.diff oms nms) (Sstr.diff nms oms) in
            Loc.errorm ~loc "Field %s is missing in some constructors"
              (Sstr.choose df) in
        let csl = match csl with
          | (_, id, pjl)::csl ->
              let oms, pjl = Lists.map_fold_left get_pj Sstr.empty pjl in
              (create_user_id id, pjl) :: List.map (get_cs oms) csl
          | [] -> assert false in
        if not (Hstr.mem htd x) then
        begin match try Some (Hstr.find hts x) with Not_found -> None with
        | Some s ->
            Hstr.add htd x (create_rec_variant_decl s csl)
        | None ->
            let itd = create_flat_variant_decl id args csl in
            Hstr.add hts x itd.itd_its; Hstr.add htd x itd end
    | TDrecord fl ->
        let alias = Sstr.empty in
        let alg = Mstr.add x (id,args) alg in
        let get_fd nms fd =
          let {id_str = nm; id_loc = loc} = fd.f_ident in
          let exn = Loc.Located (loc, Loc.Message ("Field " ^
            nm ^ " is used more than once in a record")) in
          let nms = Sstr.add_new exn nm nms in
          let id = create_user_id fd.f_ident in
          let ity = parse ~loc ~alias ~alg fd.f_pty in
          let ghost = d.td_vis = Abstract || fd.f_ghost in
          nms, (fd.f_mutable, create_pvsymbol id ~ghost ity) in
        let _,fl = Lists.map_fold_left get_fd Sstr.empty fl in
        if not (Hstr.mem htd x) then
        begin match try Some (Hstr.find hts x) with Not_found -> None with
        | Some s ->
            if d.td_vis <> Public || d.td_mut then Loc.errorm ~loc
              "Recursive types cannot be abstract, private. or mutable";
            if d.td_inv <> [] then Loc.errorm ~loc
              "Recursive types cannot have invariants";
            let get_fd (mut, fd) = if mut then Loc.errorm ~loc
              "Recursive types cannot have mutable fields" else fd in
            Hstr.add htd x (create_rec_record_decl s (List.map get_fd fl))
        | None ->
            let priv = d.td_vis <> Public and mut = d.td_mut in
            let add_fd m (_, v) = Mstr.add v.pv_vs.vs_name.id_string v m in
            let gvars = List.fold_left add_fd Mstr.empty fl in
            let type_inv f = type_fmla_pure muc gvars Dterm.denv_empty f in
            let invl = List.map type_inv d.td_inv in
            let itd = create_flat_record_decl id args priv mut fl invl in
            Hstr.add hts x itd.itd_its; Hstr.add htd x itd end

  and parse ~loc ~alias ~alg pty =
    let rec down = function
      | PTtyvar id ->
          ity_var (tv_of_string id.id_str)
      | PTtyapp (q,tyl) ->
          let s = match q with
            | Qident {id_str = x} when Sstr.mem x alias ->
                Loc.errorm ~loc "Cyclic type definition"
            | Qident {id_str = x} when Hstr.mem hts x ->
                Hstr.find hts x
            | Qident {id_str = x} when Mstr.mem x alg ->
                let id, args = Mstr.find x alg in
                let s = create_itysymbol_pure id args in
                Hstr.add hts x s;
                visit ~alias ~alg x (Mstr.find x def);
                s
            | Qident {id_str = x} when Mstr.mem x def ->
                visit ~alias ~alg x (Mstr.find x def);
                Hstr.find hts x
            | _ ->
                find_itysymbol muc q in
          Loc.try2 ~loc:(qloc q) ity_app_fresh s (List.map down tyl)
      | PTtuple tyl -> ity_tuple (List.map down tyl)
      | PTarrow (ty1,ty2) -> ity_func (down ty1) (down ty2)
      | PTparen ty -> down ty in
    down pty in

  Mstr.iter (visit ~alias:Mstr.empty ~alg:Mstr.empty) def;
  let tdl = List.map (fun d -> Hstr.find htd d.td_ident.id_str) tdl in
  add_pdecl ~vc:true muc (create_type_decl tdl)

let tyl_of_params {muc_theory = tuc} pl =
  let ty_of_param (loc,_,gh,ty) =
    if gh then Loc.errorm ~loc
      "ghost parameters are not allowed in pure declarations";
    ty_of_pty tuc ty in
  List.map ty_of_param pl

let add_logics muc dl =
  let lsymbols = Hstr.create 17 in
  (* 1. create all symbols and make an environment with these symbols *)
  let create_symbol mkk d =
    let id = d.ld_ident.id_str in
    let v = create_user_id d.ld_ident in
    let pl = tyl_of_params muc d.ld_params in
    let ty = Opt.map (ty_of_pty muc.muc_theory) d.ld_type in
    let ls = create_lsymbol v pl ty in
    Hstr.add lsymbols id ls;
    Loc.try2 ~loc:d.ld_loc add_decl mkk (create_param_decl ls) in
  let mkk = List.fold_left create_symbol muc dl in
  (* 2. then type-check all definitions *)
  let type_decl d (abst,defn) =
    let id = d.ld_ident.id_str in
    let ls = Hstr.find lsymbols id in
    let create_var (loc,x,_,_) ty =
      let id = match x with
        | Some id -> create_user_id id
        | None -> id_user "_" loc in
      create_vsymbol id ty in
    let vl = List.map2 create_var d.ld_params ls.ls_args in
    let add_var mvs (_,x,_,_) vs = match x with
      | Some {id_str = x} -> Mstr.add_new (DuplicateVar x) x (DTgvar vs) mvs
      | None -> mvs in
    let denv = List.fold_left2 add_var Dterm.denv_empty d.ld_params vl in
    match d.ld_def, d.ld_type with
    | None, _ -> ls :: abst, defn
    | Some e, None -> (* predicate *)
        let f = type_fmla_pure mkk Mstr.empty denv e in
        abst, (make_ls_defn ls vl f) :: defn
    | Some e, Some ty -> (* function *)
        let e = { e with term_desc = Tcast (e, ty) } in
        let t = type_term_pure mkk Mstr.empty denv e in
        abst, (make_ls_defn ls vl t) :: defn in
  let abst,defn = List.fold_right type_decl dl ([],[]) in
  let add_param muc s = add_decl muc (create_param_decl s) in
  let add_logic muc l = add_decl muc (create_logic_decl l) in
  let muc = List.fold_left add_param muc abst in
  if defn = [] then muc else add_logic muc defn

let add_inductives muc s dl =
  (* 1. create all symbols and make an environment with these symbols *)
  let psymbols = Hstr.create 17 in
  let create_symbol mkk d =
    let id = d.in_ident.id_str in
    let v = create_user_id d.in_ident in
    let pl = tyl_of_params muc d.in_params in
    let ps = create_psymbol v pl in
    Hstr.add psymbols id ps;
    Loc.try2 ~loc:d.in_loc add_decl mkk (create_param_decl ps) in
  let mkk = List.fold_left create_symbol muc dl in
  (* 2. then type-check all definitions *)
  let propsyms = Hstr.create 17 in
  let type_decl d =
    let id = d.in_ident.id_str in
    let ps = Hstr.find psymbols id in
    let clause (loc, id, f) =
      Hstr.replace propsyms id.id_str loc;
      let f = type_fmla_pure mkk Mstr.empty Dterm.denv_empty f in
      create_prsymbol (create_user_id id), f in
    ps, List.map clause d.in_def in
  let loc_of_id id = Opt.get id.Ident.id_loc in
  try add_decl muc (create_ind_decl s (List.map type_decl dl))
  with
  | ClashSymbol s ->
      Loc.error ~loc:(Hstr.find propsyms s) (ClashSymbol s)
  | InvalidIndDecl (ls,pr) ->
      Loc.error ~loc:(loc_of_id pr.pr_name) (InvalidIndDecl (ls,pr))
  | NonPositiveIndDecl (ls,pr,s) ->
      Loc.error ~loc:(loc_of_id pr.pr_name) (NonPositiveIndDecl (ls,pr,s))

let add_prop muc k s f =
  let pr = create_prsymbol (create_user_id s) in
  let f = type_fmla_pure muc Mstr.empty Dterm.denv_empty f in
  add_decl muc (create_prop_decl k pr f)

(* parse declarations *)

let add_decl muc d =
  let vc = muc.muc_path = [] &&
    Debug.test_noflag debug_type_only in
  match d with
  | Ptree.Dtype dl ->
      add_types muc dl
  | Ptree.Dlogic dl ->
      add_logics muc dl
  | Ptree.Dind (s,dl) ->
      add_inductives muc s dl
  | Ptree.Dprop (k,s,f) ->
      add_prop muc k s f
  | Ptree.Dmeta (id,al) ->
      let tuc = muc.muc_theory in
      let convert = function
        | Ptree.Mty (PTtyapp (q,[]))
                       -> MAts (find_tysymbol tuc q)
        | Ptree.Mty ty -> MAty (ty_of_pty tuc ty)
        | Ptree.Mfs q  -> MAls (find_fsymbol tuc q)
        | Ptree.Mps q  -> MAls (find_psymbol tuc q)
        | Ptree.Max q  -> MApr (find_prop_of_kind Paxiom tuc q)
        | Ptree.Mlm q  -> MApr (find_prop_of_kind Plemma tuc q)
        | Ptree.Mgl q  -> MApr (find_prop_of_kind Pgoal  tuc q)
        | Ptree.Mstr s -> MAstr s
        | Ptree.Mint i -> MAint i in
      add_meta muc (lookup_meta id.id_str) (List.map convert al)
  | Ptree.Dlet (id, gh, kind, e) ->
      let ld = create_user_id id, gh, kind, dexpr muc denv_empty e in
      add_pdecl ~vc muc (create_let_decl (let_defn ~keep_loc:true ld))
  | Ptree.Drec fdl ->
      let _, rd = drec_defn muc denv_empty fdl in
      add_pdecl ~vc muc (create_let_decl (rec_defn ~keep_loc:true rd))
  | Ptree.Dexn (id, pty) ->
      let ity = ity_of_pty muc pty in
      let xs = create_xsymbol (create_user_id id) ity in
      add_pdecl ~vc muc (create_exn_decl xs)

(* TODO
let rec clone_ns kn sl path ns2 ns1 s =
  let qualid fmt path = Pp.print_list
    (fun fmt () -> Format.pp_print_char fmt '.')
    Format.pp_print_string fmt (List.rev path) in
  let s = Mstr.fold (fun nm ns1 acc ->
    let ns2 = Mstr.find_def empty_ns nm ns2.ns_ns in
    clone_ns kn sl (nm::path) ns2 ns1 acc) ns1.ns_ns s
  in
  let inst_ts = Mstr.fold (fun nm ts1 acc ->
    match Mstr.find_opt nm ns2.ns_ts with
    | Some ts2 when ts_equal ts1 ts2 -> acc
    | Some _ when not (Sid.mem ts1.ts_name sl) ->
        raise (NonLocal ts1.ts_name)
    | Some _ when ts1.ts_def <> None ->
        raise (CannotInstantiate ts1.ts_name)
    | Some ts2 ->
        begin match (Mid.find ts1.ts_name kn).d_node with
          | Decl.Dtype _ -> Mts.add_new (ClashSymbol nm) ts1 ts2 acc
          | _ -> raise (CannotInstantiate ts1.ts_name)
        end
    | None when not (Sid.mem ts1.ts_name sl) -> acc
    | None when ts1.ts_def <> None -> acc
    | None ->
        begin match (Mid.find ts1.ts_name kn).d_node with
          | Decl.Dtype _ -> Loc.errorm
              "type symbol %a not found in the target theory"
              qualid (nm::path)
          | _ -> acc
        end)
    ns1.ns_ts s.inst_ts
  in
  let inst_ls = Mstr.fold (fun nm ls1 acc ->
    match Mstr.find_opt nm ns2.ns_ls with
    | Some ls2 when ls_equal ls1 ls2 -> acc
    | Some _ when not (Sid.mem ls1.ls_name sl) ->
       raise (NonLocal ls1.ls_name)
    | Some ls2 ->
        begin match (Mid.find ls1.ls_name kn).d_node with
          | Decl.Dparam _ -> Mls.add_new (ClashSymbol nm) ls1 ls2 acc
          | _ -> raise (CannotInstantiate ls1.ls_name)
        end
    | None when not (Sid.mem ls1.ls_name sl) -> acc
    | None ->
        begin match (Mid.find ls1.ls_name kn).d_node with
          | Decl.Dparam _ -> Loc.errorm
              "%s symbol %a not found in the target theory"
              (if ls1.ls_value <> None then "function" else "predicate")
              qualid (nm::path)
          | _ -> acc
        end)
    ns1.ns_ls s.inst_ls
  in
  { s with inst_ts = inst_ts; inst_ls = inst_ls }

let find_namespace_ns ns q =
  find_qualid (fun _ -> Glob.dummy_id) ns_find_ns ns q

let type_inst tuc t s =
  let add_inst s = function
    | CSns (loc,p,q) ->
      let ns1 = Opt.fold find_namespace_ns t.th_export p in
      let ns2 = Opt.fold find_namespace_ns (get_namespace tuc) q in
      Loc.try6 ~loc clone_ns t.th_known t.th_local [] ns2 ns1 s
    | CStsym (loc,p,[],PTtyapp (q,[])) ->
      let ts1 = find_tysymbol_ns t.th_export p in
      let ts2 = find_tysymbol tuc q in
      if Mts.mem ts1 s.inst_ts
      then Loc.error ~loc (ClashSymbol ts1.ts_name.id_string);
      { s with inst_ts = Mts.add ts1 ts2 s.inst_ts }
    | CStsym (loc,p,tvl,pty) ->
      let ts1 = find_tysymbol_ns t.th_export p in
      let id = id_user (ts1.ts_name.id_string ^ "_subst") loc in
      let tvl = List.map (fun id -> tv_of_string id.id_str) tvl in
      let def = Some (ty_of_pty tuc pty) in
      let ts2 = Loc.try3 ~loc create_tysymbol id tvl def in
      if Mts.mem ts1 s.inst_ts
      then Loc.error ~loc (ClashSymbol ts1.ts_name.id_string);
      { s with inst_ts = Mts.add ts1 ts2 s.inst_ts }
    | CSfsym (loc,p,q) ->
      let ls1 = find_fsymbol_ns t.th_export p in
      let ls2 = find_fsymbol tuc q in
      if Mls.mem ls1 s.inst_ls
      then Loc.error ~loc (ClashSymbol ls1.ls_name.id_string);
      { s with inst_ls = Mls.add ls1 ls2 s.inst_ls }
    | CSpsym (loc,p,q) ->
      let ls1 = find_psymbol_ns t.th_export p in
      let ls2 = find_psymbol tuc q in
      if Mls.mem ls1 s.inst_ls
      then Loc.error ~loc (ClashSymbol ls1.ls_name.id_string);
      { s with inst_ls = Mls.add ls1 ls2 s.inst_ls }
    | CSvsym (loc,_,_) ->
      Loc.errorm ~loc "program symbol instantiation \
        is not supported in pure theories"
    | CSlemma (loc,p) ->
      let pr = find_prop_ns t.th_export p in
      if Spr.mem pr s.inst_lemma || Spr.mem pr s.inst_goal
      then Loc.error ~loc (ClashSymbol pr.pr_name.id_string);
      { s with inst_lemma = Spr.add pr s.inst_lemma }
    | CSgoal (loc,p) ->
      let pr = find_prop_ns t.th_export p in
      if Spr.mem pr s.inst_lemma || Spr.mem pr s.inst_goal
      then Loc.error ~loc (ClashSymbol pr.pr_name.id_string);
      { s with inst_goal = Spr.add pr s.inst_goal }
  in
  List.fold_left add_inst empty_inst s
*)

let use_clone loc muc env file (use, subst) =
  let find_module env file q = match q with
    | Qident { id_str = id } -> (* local module *)
        begin try Mstr.find id file
        with Not_found -> read_module env [] id end
    | Qdot (p, { id_str = id }) -> (* module in file f *)
        read_module env (string_list_of_qualid p) id in
  let use_or_clone muc =
    let m = find_module env file use.use_module in
    if Debug.test_flag Glob.flag then
      Glob.use (qloc_last use.use_module) m.mod_theory.th_name;
    match subst with
    | None -> use_export muc m
    | Some _ ->
        warn_clone_not_abstract loc m.mod_theory;
        Loc.errorm ~loc "cloning coming soon" (* TODO *)
  in
  match use.use_import with
  | Some (import, use_as) ->
      (* use T = namespace T use_export T end *)
      let muc = open_namespace muc use_as in
      let muc = use_or_clone muc in
      close_namespace muc ~import
  | None ->
      use_or_clone muc

(* incremental parsing *)

type slice = {
  env           : Env.env;
  path          : Env.pathname;
  mutable file  : pmodule Mstr.t;
  mutable muc   : pmodule_uc option;
}

let state = (Stack.create () : slice Stack.t)

let open_file env path =
  assert (Stack.is_empty state || (Stack.top state).muc <> None);
  Stack.push { env = env; path = path; file = Mstr.empty; muc = None } state

let close_file () =
  assert (not (Stack.is_empty state) && (Stack.top state).muc = None);
  (Stack.pop state).file

let open_module ({id_str = nm; id_loc = loc} as id) =
  assert (not (Stack.is_empty state) && (Stack.top state).muc = None);
  let slice = Stack.top state in
  if Mstr.mem nm slice.file then Loc.errorm ~loc
    "module %s is already defined in this file" nm;
  let muc = create_module slice.env ~path:slice.path (create_user_id id) in
  slice.muc <- Some muc

let close_module loc =
  assert (not (Stack.is_empty state) && (Stack.top state).muc <> None);
  let slice = Stack.top state in
  if Debug.test_noflag debug_parse_only then begin
    let m = Loc.try1 ~loc close_module (Opt.get slice.muc) in
    if Debug.test_flag Glob.flag then Glob.def m.mod_theory.th_name;
    slice.file <- Mstr.add m.mod_theory.th_name.id_string m slice.file;
  end;
  slice.muc <- None

let open_namespace nm =
  assert (not (Stack.is_empty state) && (Stack.top state).muc <> None);
  if Debug.test_noflag debug_parse_only then
    let slice = Stack.top state in
    slice.muc <- Some (open_namespace (Opt.get slice.muc) nm.id_str)

let close_namespace loc ~import =
  assert (not (Stack.is_empty state) && (Stack.top state).muc <> None);
  if Debug.test_noflag debug_parse_only then
    let slice = Stack.top state in
    let muc = Loc.try1 ~loc (close_namespace ~import) (Opt.get slice.muc) in
    slice.muc <- Some muc

let add_decl loc d =
  assert (not (Stack.is_empty state));
  let slice = Stack.top state in
  let muc = match slice.muc with
    | Some muc -> muc
    | None ->
        assert (Mstr.is_empty slice.file);
        if slice.path <> [] then Loc.errorm ~loc
          "All declarations in library files must be inside modules";
        let muc = create_module slice.env ~path:[] (id_fresh "Top") in
        slice.muc <- Some muc;
        muc in
  if Debug.test_noflag debug_parse_only then
    let muc = Loc.try2 ~loc add_decl muc d in
    slice.muc <- Some muc

let use_clone loc use =
  assert (not (Stack.is_empty state) && (Stack.top state).muc <> None);
  if Debug.test_noflag debug_parse_only then
    let slice = Stack.top state in
    let muc = Loc.try5 ~loc use_clone loc
      (Opt.get slice.muc) slice.env slice.file use in
    slice.muc <- Some muc

(** Exception printing *)

let () = Exn_printer.register (fun fmt e -> match e with
  | UnboundSymbol q ->
      Format.fprintf fmt "unbound symbol '%a'" print_qualid q
  | _ -> raise e)
