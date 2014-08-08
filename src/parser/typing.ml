(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2014   --   INRIA - CNRS - Paris-Sud University  *)
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
open Env

(** debug flags *)

let debug_parse_only = Debug.register_flag "parse_only"
  ~desc:"Stop@ after@ parsing."

let debug_type_only  = Debug.register_flag "type_only"
  ~desc:"Stop@ after@ type-checking."

(** errors *)

exception UnboundTypeVar of string
exception DuplicateTypeVar of string
exception ClashTheory of string

(** lazy declaration of tuples *)

let add_decl_with_tuples uc d =
  if Debug.test_flag Glob.flag then Sid.iter Glob.def d.d_news;
  add_decl_with_tuples uc d

let add_ty_decl uc ts      = add_decl_with_tuples uc (create_ty_decl ts)
let add_data_decl uc dl    = add_decl_with_tuples uc (create_data_decl dl)
let add_param_decl uc ls   = add_decl_with_tuples uc (create_param_decl ls)
let add_logic_decl uc dl   = add_decl_with_tuples uc (create_logic_decl dl)
let add_ind_decl uc s dl   = add_decl_with_tuples uc (create_ind_decl s dl)
let add_prop_decl uc k p f = add_decl_with_tuples uc (create_prop_decl k p f)

(** symbol lookup *)

let rec qloc = function
  | Qdot (p, id) -> Loc.join (qloc p) id.id_loc
  | Qident id    -> id.id_loc

let qloc_last = function
  | Qdot (_, id) | Qident id -> id.id_loc

let rec print_qualid fmt = function
  | Qdot (p, id) -> Format.fprintf fmt "%a.%s" print_qualid p id.id
  | Qident id    -> Format.fprintf fmt "%s" id.id

let string_list_of_qualid q =
  let rec sloq acc = function
    | Qdot (p, id) -> sloq (id.id :: acc) p
    | Qident id -> id.id :: acc in
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

let find_prop     uc q = find_prop_ns     (get_namespace uc) q
let find_tysymbol uc q = find_tysymbol_ns (get_namespace uc) q
let find_lsymbol  uc q = find_lsymbol_ns  (get_namespace uc) q
let find_fsymbol  uc q = find_fsymbol_ns  (get_namespace uc) q
let find_psymbol  uc q = find_psymbol_ns  (get_namespace uc) q

let find_namespace_ns ns q =
  find_qualid (fun _ -> Glob.dummy_id) ns_find_ns ns q

(** Parsing types *)

let ty_of_pty ?(noop=true) uc pty =
  let rec get_ty = function
    | PPTtyvar ({id_loc = loc}, true) when noop ->
        Loc.errorm ~loc "Opaqueness@ annotations@ are@ only@ \
          allowed@ in@ function@ and@ predicate@ prototypes"
    | PPTtyvar ({id = x}, _) ->
        ty_var (tv_of_string x)
    | PPTtyapp (q, tyl) ->
        let ts = find_tysymbol uc q in
        let tyl = List.map get_ty tyl in
        Loc.try2 ~loc:(qloc q) ty_app ts tyl
    | PPTtuple tyl ->
        let ts = ts_tuple (List.length tyl) in
        ty_app ts (List.map get_ty tyl)
    | PPTarrow (ty1, ty2) ->
        ty_func (get_ty ty1) (get_ty ty2)
    | PPTparen ty ->
        get_ty ty
  in
  get_ty pty

let opaque_tvs args =
  let rec opaque_tvs acc = function
    | PPTtyvar (id, true) -> Stv.add (tv_of_string id.id) acc
    | PPTtyvar (_, false) -> acc
    | PPTtyapp (_, pl)
    | PPTtuple pl -> List.fold_left opaque_tvs acc pl
    | PPTarrow (ty1, ty2) -> opaque_tvs (opaque_tvs acc ty1) ty2
    | PPTparen ty -> opaque_tvs acc ty in
  List.fold_left (fun acc (_,_,_,ty) -> opaque_tvs acc ty) Stv.empty args

(** typing using destructive type variables

    parsed trees        intermediate trees       typed trees
      (Ptree)                (Dterm)               (Term)
   -----------------------------------------------------------
     ppure_type  ---dty--->   dty       ---ty--->    ty
      lexpr      --dterm-->   dterm     --term-->    term
*)

(** Typing patterns, terms, and formulas *)

let create_user_id {id = n; id_lab = label; id_loc = loc} =
  let get_labels (label, loc) = function
    | Lstr lab -> Slab.add lab label, loc | Lpos loc -> label, loc in
  let label,loc = List.fold_left get_labels (Slab.empty,loc) label in
  id_user ~label n loc

let parse_record ~loc uc get_val fl =
  let fl = List.map (fun (q,e) -> find_lsymbol uc q, e) fl in
  let cs,pjl,flm = Loc.try2 ~loc parse_record (get_known uc) fl in
  let get_val pj = get_val cs pj (Mls.find_opt pj flm) in
  cs, List.map get_val pjl

let rec dpattern uc { pat_desc = desc; pat_loc = loc } =
  Dterm.dpattern ~loc (match desc with
    | PPpwild -> DPwild
    | PPpvar x -> DPvar (create_user_id x)
    | PPpapp (q,pl) ->
        let pl = List.map (dpattern uc) pl in
        DPapp (find_lsymbol uc q, pl)
    | PPptuple pl ->
        let pl = List.map (dpattern uc) pl in
        DPapp (fs_tuple (List.length pl), pl)
    | PPprec fl ->
        let get_val _ _ = function
          | Some p -> dpattern uc p
          | None -> Dterm.dpattern DPwild in
        let cs,fl = parse_record ~loc uc get_val fl in
        DPapp (cs,fl)
    | PPpas (p, x) -> DPas (dpattern uc p, create_user_id x)
    | PPpor (p, q) -> DPor (dpattern uc p, dpattern uc q))

let quant_var uc (x,ty) =
  create_user_id x, match ty with
    | Some ty -> dty_of_ty (ty_of_pty uc ty)
    | None -> dty_fresh ()

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

let chainable_op uc op =
  (* non-bool -> non-bool -> bool *)
  op.id = "infix =" || op.id = "infix <>" ||
  match find_lsymbol uc (Qident op) with
  | {ls_args = [ty1;ty2]; ls_value = ty} ->
      Opt.fold (fun _ ty -> ty_equal ty ty_bool) true ty
      && not (ty_equal ty1 ty_bool)
      && not (ty_equal ty2 ty_bool)
  | _ -> false

type global_vs = Ptree.qualid -> vsymbol option

let mk_closure loc ls =
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

let rec dterm uc gvars denv {pp_desc = desc; pp_loc = loc} =
  let func_app e el =
    List.fold_left (fun e1 (loc, e2) ->
      DTfapp (Dterm.dterm ~loc e1, e2)) e el
  in
  let rec apply_ls loc ls al l el = match l, el with
    | (_::l), (e::el) -> apply_ls loc ls (e::al) l el
    | [], _ -> func_app (DTapp (ls, List.rev_map snd al)) el
    | _, [] -> func_app (mk_closure loc ls) (List.rev_append al el)
  in
  let qualid_app q el = match gvars q with
    | Some vs -> func_app (DTgvar vs) el
    | None ->
        let ls = find_lsymbol uc q in
        apply_ls (qloc q) ls [] ls.ls_args el
  in
  let qualid_app q el = match q with
    | Qident {id = n} ->
        (match denv_get_opt denv n with
        | Some d -> func_app d el
        | None -> qualid_app q el)
    | _ -> qualid_app q el
  in
  let rec unfold_app e1 e2 el = match e1.pp_desc with
    | PPapply (e11,e12) ->
        let e12 = dterm uc gvars denv e12 in
        unfold_app e11 e12 ((e1.pp_loc, e2)::el)
    | PPident q ->
        qualid_app q ((e1.pp_loc, e2)::el)
    | _ ->
        func_app (DTfapp (dterm uc gvars denv e1, e2)) el
  in
  Dterm.dterm ~loc (match desc with
  | PPident q ->
      qualid_app q []
  | PPidapp (q, tl) ->
      let tl = List.map (dterm uc gvars denv) tl in
      DTapp (find_lsymbol uc q, tl)
  | PPapply (e1, e2) ->
      unfold_app e1 (dterm uc gvars denv e2) []
  | PPtuple tl ->
      let tl = List.map (dterm uc gvars denv) tl in
      DTapp (fs_tuple (List.length tl), tl)
  | PPinfix (e12, op2, e3)
  | PPinnfix (e12, op2, e3) ->
      let make_app de1 op de2 = if op.id = "infix <>" then
        let op = { op with id = "infix =" } in
        let ls = find_lsymbol uc (Qident op) in
        DTnot (Dterm.dterm ~loc (DTapp (ls, [de1;de2])))
      else
        DTapp (find_lsymbol uc (Qident op), [de1;de2])
      in
      let rec make_chain de1 = function
        | [op,de2] ->
            make_app de1 op de2
        | (op,de2) :: ch ->
            let de12 = Dterm.dterm ~loc (make_app de1 op de2) in
            let de23 = Dterm.dterm ~loc (make_chain de2 ch) in
            DTbinop (DTand, de12, de23)
        | [] -> assert false in
      let rec get_chain e12 acc = match e12.pp_desc with
        | PPinfix (e1, op1, e2) when chainable_op uc op1 ->
            get_chain e1 ((op1, dterm uc gvars denv e2) :: acc)
        | _ -> e12, acc in
      let ch = [op2, dterm uc gvars denv e3] in
      let e1, ch = if chainable_op uc op2
        then get_chain e12 ch else e12, ch in
      make_chain (dterm uc gvars denv e1) ch
  | PPconst c ->
      DTconst c
  | PPlet (x, e1, e2) ->
      let id = create_user_id x in
      let e1 = dterm uc gvars denv e1 in
      let denv = denv_add_let denv e1 id in
      let e2 = dterm uc gvars denv e2 in
      DTlet (e1, id, e2)
  | PPmatch (e1, bl) ->
      let e1 = dterm uc gvars denv e1 in
      let branch (p, e) =
        let p = dpattern uc p in
        let denv = denv_add_pat denv p in
        p, dterm uc gvars denv e in
      DTcase (e1, List.map branch bl)
  | PPif (e1, e2, e3) ->
      let e1 = dterm uc gvars denv e1 in
      let e2 = dterm uc gvars denv e2 in
      let e3 = dterm uc gvars denv e3 in
      DTif (e1, e2, e3)
  | PPtrue ->
      DTtrue
  | PPfalse ->
      DTfalse
  | PPunop (PPnot, e1) ->
      DTnot (dterm uc gvars denv e1)
  | PPbinop (e1, op, e2) ->
      let e1 = dterm uc gvars denv e1 in
      let e2 = dterm uc gvars denv e2 in
      let op = match op with
        | PPand -> DTand
        | PPand_asym -> DTand_asym
        | PPor -> DTor
        | PPor_asym -> DTor_asym
        | PPimplies -> DTimplies
        | PPiff -> DTiff in
      DTbinop (op, e1, e2)
  | PPquant (q, uqu, trl, e1) ->
      let qvl = List.map (quant_var uc) uqu in
      let denv = denv_add_quant denv qvl in
      let dterm e = dterm uc gvars denv e in
      let trl = List.map (List.map dterm) trl in
      let e1 = dterm e1 in
      begin match q with
        | PPforall -> DTquant (Tforall, qvl, trl, e1)
        | PPexists -> DTquant (Texists, qvl, trl, e1)
        | PPlambda ->
            let id = id_user "fc" loc and dty = dty_fresh () in
            let add acc ({id = x}, _) =
              let arg = Dterm.dterm ~loc (denv_get denv x) in
              DTapp (fs_func_app, [Dterm.dterm ~loc acc; arg]) in
            let app = List.fold_left add (DTvar ("fc",dty)) uqu in
            let f = DTapp (ps_equ, [Dterm.dterm ~loc app; e1]) in
            let f = DTquant (Tforall, qvl, trl, Dterm.dterm ~loc f) in
            DTeps (id, dty, Dterm.dterm ~loc f)
      end
  | PPrecord fl ->
      let get_val cs pj = function
        | Some e -> dterm uc gvars denv e
        | None -> Loc.error ~loc (RecordFieldMissing (cs,pj)) in
      let cs, fl = parse_record ~loc uc get_val fl in
      DTapp (cs, fl)
  | PPupdate (e1, fl) ->
      let e1 = dterm uc gvars denv e1 in
      let re = is_reusable e1 in
      let v = if re then e1 else mk_var "_q " e1 in
      let get_val _ pj = function
        | Some e -> dterm uc gvars denv e
        | None -> Dterm.dterm ~loc (DTapp (pj,[v])) in
      let cs, fl = parse_record ~loc uc get_val fl in
      let d = DTapp (cs, fl) in
      if re then d else mk_let ~loc "_q " e1 d
  | PPnamed (Lpos uloc, e1) ->
      DTuloc (dterm uc gvars denv e1, uloc)
  | PPnamed (Lstr lab, e1) ->
      DTlabel (dterm uc gvars denv e1, Slab.singleton lab)
  | PPcast (e1, ty) ->
      DTcast (dterm uc gvars denv e1, ty_of_pty uc ty))

(** Export for program parsing *)

let type_term uc gvars t =
  let t = dterm uc gvars denv_empty t in
  Dterm.term ~strict:true ~keep_loc:true t

let type_fmla uc gvars f =
  let f = dterm uc gvars denv_empty f in
  Dterm.fmla ~strict:true ~keep_loc:true f

(** Typing declarations *)

let tyl_of_params ?(noop=false) uc pl =
  let ty_of_param (loc,_,gh,ty) =
    if gh then Loc.errorm ~loc
      "ghost parameters are not allowed in pure declarations";
    ty_of_pty ~noop uc ty in
  List.map ty_of_param pl

let add_types dl th =
  let def = List.fold_left
    (fun def d ->
      let id = d.td_ident.id in
      Mstr.add_new (Loc.Located (d.td_loc, ClashSymbol id)) id d def)
    Mstr.empty dl
  in
  let tysymbols = Hstr.create 17 in
  let rec visit x =
    let d = Mstr.find x def in
    try
      match Hstr.find tysymbols x with
        | None -> Loc.errorm ~loc:d.td_loc "Cyclic type definition"
        | Some ts -> ts
    with Not_found ->
      Hstr.add tysymbols x None;
      let vars = Hstr.create 17 in
      let vl = List.map (fun id ->
        if Hstr.mem vars id.id then
          Loc.error ~loc:id.id_loc (DuplicateTypeVar id.id);
        let i = tv_of_string id.id in
        Hstr.add vars id.id i;
        i) d.td_params
      in
      let id = create_user_id d.td_ident in
      let ts = match d.td_def with
        | TDalias ty ->
            let rec apply = function
              | PPTtyvar (v, _) ->
                  begin
                    try ty_var (Hstr.find vars v.id) with Not_found ->
                      Loc.error ~loc:v.id_loc (UnboundTypeVar v.id)
                  end
              | PPTtyapp (q, tyl) ->
                  let ts = match q with
                    | Qident x when Mstr.mem x.id def ->
                        visit x.id
                    | Qident _ | Qdot _ ->
                        find_tysymbol th q
                  in
                  Loc.try2 ~loc:(qloc q) ty_app ts (List.map apply tyl)
              | PPTtuple tyl ->
                  let ts = ts_tuple (List.length tyl) in
                  ty_app ts (List.map apply tyl)
              | PPTarrow (ty1, ty2) ->
                  ty_func (apply ty1) (apply ty2)
              | PPTparen ty ->
                  apply ty
            in
            create_tysymbol id vl (Some (apply ty))
        | TDabstract | TDalgebraic _ ->
            create_tysymbol id vl None
        | TDrecord _ ->
            assert false
      in
      Hstr.add tysymbols x (Some ts);
      ts
  in
  let th' =
    let add_ts (abstr,alias) d =
      let ts = visit d.td_ident.id in
      if ts.ts_def = None then ts::abstr, alias else abstr, ts::alias in
    let abstr,alias = List.fold_left add_ts ([],[]) dl in
    try
      let th = List.fold_left add_ty_decl th abstr in
      let th = List.fold_left add_ty_decl th alias in
      th
    with ClashSymbol s ->
      Loc.error ~loc:(Mstr.find s def).td_loc (ClashSymbol s)
  in
  let csymbols = Hstr.create 17 in
  let decl d (abstr,algeb,alias) =
    let ts = match Hstr.find tysymbols d.td_ident.id with
      | None ->
          assert false
      | Some ts ->
          ts
    in
    match d.td_def with
      | TDabstract -> ts::abstr, algeb, alias
      | TDalias _ -> abstr, algeb, ts::alias
      | TDalgebraic cl ->
          let ht = Hstr.create 17 in
          let constr = List.length cl in
          let opaque = Stv.of_list ts.ts_args in
          let ty = ty_app ts (List.map ty_var ts.ts_args) in
          let projection (_,id,_,_) fty = match id with
            | None -> None
            | Some ({ id = x; id_loc = loc } as id) ->
                try
                  let pj = Hstr.find ht x in
                  let ty = Opt.get pj.ls_value in
                  ignore (Loc.try2 ~loc ty_equal_check ty fty);
                  Some pj
                with Not_found ->
                  let fn = create_user_id id in
                  let pj = create_fsymbol ~opaque fn [ty] fty in
                  Hstr.replace csymbols x loc;
                  Hstr.replace ht x pj;
                  Some pj
          in
          let constructor (loc, id, pl) =
            let tyl = tyl_of_params ~noop:true th' pl in
            let pjl = List.map2 projection pl tyl in
            Hstr.replace csymbols id.id loc;
            create_fsymbol ~opaque ~constr (create_user_id id) tyl ty, pjl
          in
          abstr, (ts, List.map constructor cl) :: algeb, alias
      | TDrecord _ ->
          assert false
  in
  let abstr,algeb,alias = List.fold_right decl dl ([],[],[]) in
  try
    let th = List.fold_left add_ty_decl th abstr in
    let th = if algeb = [] then th else add_data_decl th algeb in
    let th = List.fold_left add_ty_decl th alias in
    th
  with
    | ClashSymbol s ->
        Loc.error ~loc:(Hstr.find csymbols s) (ClashSymbol s)
    | RecordFieldMissing ({ ls_name = { id_string = s }} as cs,ls) ->
        Loc.error ~loc:(Hstr.find csymbols s) (RecordFieldMissing (cs,ls))
    | DuplicateRecordField ({ ls_name = { id_string = s }} as cs,ls) ->
        Loc.error ~loc:(Hstr.find csymbols s) (DuplicateRecordField (cs,ls))

let prepare_typedef td =
  if td.td_model then
    Loc.errorm ~loc:td.td_loc "model types are not allowed in pure theories";
  if td.td_vis <> Public then
    Loc.errorm ~loc:td.td_loc "pure types cannot be abstract or private";
  if td.td_inv <> [] then
    Loc.errorm ~loc:td.td_loc "pure types cannot have invariants";
  match td.td_def with
  | TDabstract | TDalgebraic _ | TDalias _ ->
      td
  | TDrecord fl ->
      let field { f_loc = loc; f_ident = id; f_pty = ty;
                  f_mutable = mut; f_ghost = gh } =
        if mut then Loc.errorm ~loc "a logic record field cannot be mutable";
        if gh then Loc.errorm ~loc "a logic record field cannot be ghost";
        loc, Some id, false, ty
      in
      (* constructor for type t is "mk t" (and not String.capitalize t) *)
      let id = { td.td_ident with id = "mk " ^ td.td_ident.id } in
      { td with td_def = TDalgebraic [td.td_loc, id, List.map field fl] }

let add_types dl th =
  add_types (List.map prepare_typedef dl) th

let add_logics dl th =
  let lsymbols = Hstr.create 17 in
  (* 1. create all symbols and make an environment with these symbols *)
  let create_symbol th d =
    let id = d.ld_ident.id in
    let v = create_user_id d.ld_ident in
    let pl = tyl_of_params th d.ld_params in
    let ty = Opt.map (ty_of_pty th) d.ld_type in
    let opaque = opaque_tvs d.ld_params in
    (* for abstract lsymbols fresh tyvars are opaque *)
    let opaque = if d.ld_def = None && ty <> None then
      let atvs = List.fold_left ty_freevars Stv.empty pl in
      let vtvs = oty_freevars Stv.empty ty in
      Stv.union opaque (Stv.diff vtvs atvs)
    else opaque in
    let ls = create_lsymbol ~opaque v pl ty in
    Hstr.add lsymbols id ls;
    Loc.try2 ~loc:d.ld_loc add_param_decl th ls
  in
  let th' = List.fold_left create_symbol th dl in
  (* 2. then type-check all definitions *)
  let type_decl d (abst,defn) =
    let id = d.ld_ident.id in
    let ls = Hstr.find lsymbols id in
    let create_var (loc,x,_,_) ty =
      let id = match x with
        | Some id -> create_user_id id
        | None -> id_user "_" loc in
      create_vsymbol id ty in
    let vl = List.map2 create_var d.ld_params ls.ls_args in
    let add_var mvs (_,x,_,_) vs = match x with
      | Some {id = id} -> Mstr.add_new (DuplicateVar id) id (DTgvar vs) mvs
      | None -> mvs in
    let denv = List.fold_left2 add_var denv_empty d.ld_params vl in
    match d.ld_def, d.ld_type with
    | None, _ -> ls :: abst, defn
    | Some e, None -> (* predicate *)
        let f = dterm th' (fun _ -> None) denv e in
        let f = fmla ~strict:true ~keep_loc:true f in
        abst, (ls, vl, f) :: defn
    | Some e, Some ty -> (* function *)
        let e = { e with pp_desc = PPcast (e, ty) } in
        let t = dterm th' (fun _ -> None) denv e in
        let t = term ~strict:true ~keep_loc:true t in
        abst, (ls, vl, t) :: defn
  in
  let abst,defn = List.fold_right type_decl dl ([],[]) in
  (* 3. detect opacity *)
  let ldefns defn =
    let ht = Hls.create 3 in
    let add_ls (ls,_,_) =
      let tvs = oty_freevars Stv.empty ls.ls_value in
      let tvs = List.fold_left ty_freevars tvs ls.ls_args in
      Hls.replace ht ls tvs in
    List.iter add_ls defn;
    let compared s ls args value =
      let sbs = oty_match Mtv.empty ls.ls_value value in
      let sbs = List.fold_left2 ty_match sbs ls.ls_args args in
      let opq = try Hls.find ht ls with Not_found -> ls.ls_opaque in
      Mtv.fold (fun _ ty s -> ty_freevars s ty) (Mtv.set_diff sbs opq) s in
    let check_ld fixp (ls,_,t) =
      let opq = Hls.find ht ls in
      let npq = Stv.diff opq (t_app_fold compared Stv.empty t) in
      Hls.replace ht ls npq;
      fixp && Stv.equal opq npq in
    let rec fixp () =
      if not (List.fold_left check_ld true defn) then fixp () in
    fixp ();
    let mk_sbs sbs ({ls_name = id} as ls,_,_) =
      let opaque = Stv.union ls.ls_opaque (Hls.find ht ls) in
      if Stv.equal ls.ls_opaque opaque then sbs else
      let nls = create_lsymbol ~opaque (id_clone id) ls.ls_args ls.ls_value in
      Mls.add ls nls sbs in
    let sbs = List.fold_left mk_sbs Mls.empty defn in
    let mk_ld (ls,vl,t) =
      let get_ls ls = Mls.find_def ls ls sbs in
      make_ls_defn (get_ls ls) vl (t_s_map (fun ty -> ty) get_ls t) in
    List.map mk_ld defn
  in
  let th = List.fold_left add_param_decl th abst in
  let th = if defn = [] then th else add_logic_decl th (ldefns defn) in
  th

let add_prop k loc s f th =
  let pr = create_prsymbol (create_user_id s) in
  let f = type_fmla th (fun _ -> None) f in
  Loc.try4 ~loc add_prop_decl th k pr f

let loc_of_id id = Opt.get id.Ident.id_loc

let add_inductives s dl th =
  (* 1. create all symbols and make an environment with these symbols *)
  let psymbols = Hstr.create 17 in
  let create_symbol th d =
    let id = d.in_ident.id in
    let v = create_user_id d.in_ident in
    let pl = tyl_of_params th d.in_params in
    let opaque = opaque_tvs d.in_params in
    let ps = create_psymbol ~opaque v pl in
    Hstr.add psymbols id ps;
    Loc.try2 ~loc:d.in_loc add_param_decl th ps
  in
  let th' = List.fold_left create_symbol th dl in
  (* 2. then type-check all definitions *)
  let propsyms = Hstr.create 17 in
  let type_decl d =
    let id = d.in_ident.id in
    let ps = Hstr.find psymbols id in
    let clause (loc, id, f) =
      Hstr.replace propsyms id.id loc;
      let f = type_fmla th' (fun _ -> None) f in
      create_prsymbol (create_user_id id), f
    in
    ps, List.map clause d.in_def
  in
  try add_ind_decl th s (List.map type_decl dl)
  with
  | ClashSymbol s ->
      Loc.error ~loc:(Hstr.find propsyms s) (ClashSymbol s)
  | InvalidIndDecl (ls,pr) ->
      Loc.error ~loc:(loc_of_id pr.pr_name) (InvalidIndDecl (ls,pr))
  | NonPositiveIndDecl (ls,pr,s) ->
      Loc.error ~loc:(loc_of_id pr.pr_name) (NonPositiveIndDecl (ls,pr,s))

(* parse declarations *)

let prop_kind = function
  | Kaxiom -> Paxiom
  | Kgoal -> Pgoal
  | Klemma -> Plemma

let find_theory env lenv q = match q with
  | Qident { id = id } -> (* local theory *)
      begin try Mstr.find id lenv
      with Not_found -> read_lib_theory env [] id end
  | Qdot (p, { id = id }) -> (* theory in file f *)
      read_lib_theory env (string_list_of_qualid p) id

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

let add_decl loc th = function
  | Ptree.TypeDecl dl ->
      add_types dl th
  | Ptree.LogicDecl dl ->
      add_logics dl th
  | Ptree.IndDecl (s, dl) ->
      add_inductives s dl th
  | Ptree.PropDecl (k, s, f) ->
      add_prop (prop_kind k) loc s f th
  | Ptree.Meta (id, al) ->
      let convert = function
        | PMAty (PPTtyapp (q,[]))
                   -> MAts (find_tysymbol th q)
        | PMAty ty -> MAty (ty_of_pty th ty)
        | PMAfs q  -> MAls (find_fsymbol th q)
        | PMAps q  -> MAls (find_psymbol th q)
        | PMApr q  -> MApr (find_prop th q)
        | PMAstr s -> MAstr s
        | PMAint i -> MAint i
      in
      let add s = add_meta th (lookup_meta s) (List.map convert al) in
      Loc.try1 ~loc add id.id

let add_decl loc th d =
  if Debug.test_flag debug_parse_only then th else
  Loc.try3 ~loc add_decl loc th d

let type_inst th t s =
  let add_inst s = function
    | CSns (loc,p,q) ->
      let ns1 = Opt.fold find_namespace_ns t.th_export p in
      let ns2 = Opt.fold find_namespace_ns (get_namespace th) q in
      Loc.try6 ~loc clone_ns t.th_known t.th_local [] ns2 ns1 s
    | CStsym (loc,p,[],PPTtyapp (q,[])) ->
      let ts1 = find_tysymbol_ns t.th_export p in
      let ts2 = find_tysymbol th q in
      if Mts.mem ts1 s.inst_ts
      then Loc.error ~loc (ClashSymbol ts1.ts_name.id_string);
      { s with inst_ts = Mts.add ts1 ts2 s.inst_ts }
    | CStsym (loc,p,tvl,pty) ->
      let ts1 = find_tysymbol_ns t.th_export p in
      let id = id_user (ts1.ts_name.id_string ^ "_subst") loc in
      let tvl = List.map (fun id -> tv_of_string id.id) tvl in
      let def = Some (ty_of_pty th pty) in
      let ts2 = Loc.try3 ~loc create_tysymbol id tvl def in
      if Mts.mem ts1 s.inst_ts
      then Loc.error ~loc (ClashSymbol ts1.ts_name.id_string);
      { s with inst_ts = Mts.add ts1 ts2 s.inst_ts }
    | CSfsym (loc,p,q) ->
      let ls1 = find_fsymbol_ns t.th_export p in
      let ls2 = find_fsymbol th q in
      if Mls.mem ls1 s.inst_ls
      then Loc.error ~loc (ClashSymbol ls1.ls_name.id_string);
      { s with inst_ls = Mls.add ls1 ls2 s.inst_ls }
    | CSpsym (loc,p,q) ->
      let ls1 = find_psymbol_ns t.th_export p in
      let ls2 = find_psymbol th q in
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

let add_use_clone env lenv th loc (use, subst) =
  if Debug.test_flag debug_parse_only then th else
  let use_or_clone th =
    let t = find_theory env lenv use.use_theory in
    if Debug.test_flag Glob.flag then
      Glob.use (qloc_last use.use_theory) t.th_name;
    match subst with
    | None -> use_export th t
    | Some s ->
        warn_clone_not_abstract loc t;
        clone_export th t (type_inst th t s)
  in
  let use_or_clone th = match use.use_import with
    | Some (import, use_as) ->
        (* use T = namespace T use_export T end *)
        let th = open_namespace th use_as in
        let th = use_or_clone th in
        close_namespace th import
    | None ->
        use_or_clone th
  in
  Loc.try1 ~loc use_or_clone th

let close_theory lenv th =
  if Debug.test_flag debug_parse_only then lenv else
  let th = close_theory th in
  if Debug.test_flag Glob.flag then Glob.def th.th_name;
  let id = th.th_name.id_string in
  let loc = th.th_name.Ident.id_loc in
  if Mstr.mem id lenv then Loc.error ?loc (ClashTheory id);
  Mstr.add id th lenv

let close_namespace loc import th =
  Loc.try2 ~loc close_namespace th import

(* incremental parsing *)

let open_file, close_file =
  let lenv = Stack.create () in
  let uc   = Stack.create () in
  let open_file env path =
    Stack.push Mstr.empty lenv;
    let open_theory id =
      Stack.push (Theory.create_theory ~path (create_user_id id)) uc in
    let close_theory () =
      Stack.push (close_theory (Stack.pop lenv) (Stack.pop uc)) lenv in
    let open_namespace name =
      Stack.push (Theory.open_namespace (Stack.pop uc) name) uc in
    let close_namespace loc imp =
      Stack.push (close_namespace loc imp (Stack.pop uc)) uc in
    let new_decl loc d =
      Stack.push (add_decl loc (Stack.pop uc) d) uc in
    let use_clone loc use =
      let lenv = Stack.top lenv in
      Stack.push (add_use_clone env lenv (Stack.pop uc) loc use) uc in
    { open_theory = open_theory;
      close_theory = close_theory;
      open_namespace = open_namespace;
      close_namespace = close_namespace;
      new_decl = new_decl;
      use_clone = use_clone;
      open_module = (fun _ -> assert false);
      close_module = (fun _ -> assert false);
      new_pdecl = (fun _ -> assert false); }
  in
  let close_file () = Stack.pop lenv in
  open_file, close_file

(** Exception printing *)

let () = Exn_printer.register (fun fmt e -> match e with
  | UnboundSymbol q ->
      Format.fprintf fmt "unbound symbol '%a'" print_qualid q
  | UnboundTypeVar s ->
      Format.fprintf fmt "unbound type variable '%s" s
  | DuplicateTypeVar s ->
      Format.fprintf fmt "duplicate type parameter '%s" s
  | ClashTheory s ->
      Format.fprintf fmt "clash with previous theory %s" s
  | _ -> raise e)

(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
