(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2017   --   INRIA - CNRS - Paris-Sud University  *)
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
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

type constructor = plsymbol * plsymbol option list

type data_decl = itysymbol * constructor list * post

type pdecl = {
  pd_node : pdecl_node;
  pd_syms : Sid.t;         (* idents used in declaration *)
  pd_news : Sid.t;         (* idents introduced in declaration *)
  pd_tag  : int;           (* unique tag *)
}

and pdecl_node =
  | PDtype of itysymbol
  | PDdata of data_decl list
  | PDval  of let_sym
  | PDlet  of let_defn
  | PDrec  of fun_defn list
  | PDexn  of xsymbol

let pd_equal : pdecl -> pdecl -> bool = (==)

let ts_mark = create_tysymbol (id_fresh "'mark") [] NoDef
let ty_mark = ty_app ts_mark []
let ity_mark = ity_pur ts_mark []

let pv_old = create_pvsymbol ~ghost:true (id_fresh "%old") ity_mark

let mk_decl =
  let r = ref 0 in
  fun node syms news ->
    incr r;
    let syms = Sid.remove pv_old.pv_vs.vs_name syms in
    { pd_node = node; pd_syms = syms; pd_news = news; pd_tag = !r; }

let news_id s id = Sid.add_new (Decl.ClashIdent id) id s

(** {2 Declaration constructors} *)

let create_ty_decl its =
  let news = Sid.singleton its.its_ts.ts_name in
  (* an abstract type must be declared using Decl.create_ty_decl *)
  if its.its_def = None then invalid_arg "Mlw_decl.create_ty_decl";
  mk_decl (PDtype its) Sid.empty news

type pre_field = preid option * field

type pre_constructor = preid * pre_field list

type pre_data_decl = itysymbol * pre_constructor list

let null_invariant { its_ts = ts } =
  let ty = ty_app ts (List.map ty_var ts.ts_args) in
  let vs = create_vsymbol (id_fresh "dummy") ty in
  create_post vs t_true

let create_data_decl tdl =
  let news = ref Sid.empty in
  let build_type (its,cl) =
    news := news_id !news its.its_ts.ts_name;
    let projections = Hstr.create 3 in
    let hidden = its.its_abst in
    let rdonly = its.its_priv in
    let constr = List.length cl in
    let tvl = List.map ity_var its.its_ts.ts_args in
    let ity = ity_app its tvl its.its_regs in
    let res = { fd_ity = ity; fd_ghost = false; fd_mut = None } in
    let tvs = List.fold_right Stv.add its.its_ts.ts_args Stv.empty in
    let regs = List.fold_right Sreg.add its.its_regs Sreg.empty in
    let nogh = ity_nonghost_reg Sreg.empty ity in
    let build_constructor (id,al) =
      (* check well-formedness *)
      let fds = List.map snd al in
      let check_vars { vars_tv = atvs; vars_reg = aregs } =
        if not (Stv.subset atvs tvs) then
          raise (UnboundTypeVar (Stv.choose (Stv.diff atvs tvs)));
        if not (Sreg.subset aregs regs) then
          raise (UnboundRegion (Sreg.choose (Sreg.diff aregs regs))) in
      let check_vars fd = match fd.fd_mut with
        | Some r -> if not (Sreg.mem r regs) then raise (UnboundRegion r)
        | None -> check_vars fd.fd_ity.ity_vars in
      let check_ghost fd =
        let regs = ity_nonghost_reg Sreg.empty fd.fd_ity in
        let regs = Opt.fold_right Sreg.add fd.fd_mut regs in
        if not (Sreg.subset regs nogh) then
          invalid_arg "Mlw_decl.create_data_decl" in
      let check_fd fd =
        if not fd.fd_ghost then check_ghost fd;
        check_vars fd in
      List.iter check_fd fds;
      (* build the constructor symbol *)
      let cs = create_plsymbol ~hidden ~rdonly ~constr id fds res in
      news := news_id !news cs.pl_ls.ls_name;
      (* build the projections, if any *)
      let build_proj fd id =
        try
          let pj = Hstr.find projections id.pre_name in
          ity_equal_check pj.pl_value.fd_ity fd.fd_ity;
          begin match pj.pl_value.fd_mut, fd.fd_mut with
            | None, None -> ()
            | Some r1, Some r2 -> reg_equal_check r1 r2
            | _,_ -> invalid_arg "Mlw_decl.create_data_decl"
          end;
          if pj.pl_value.fd_ghost <> fd.fd_ghost then
            invalid_arg "Mlw_decl.create_data_decl";
          pj
        with Not_found ->
          let pj = create_plsymbol ~hidden id [res] fd in
          news := news_id !news pj.pl_ls.ls_name;
          Hstr.add projections id.pre_name pj;
          pj
      in
      cs, List.map (fun (id,fd) -> Opt.map (build_proj fd) id) al
    in
    its, List.map build_constructor cl, null_invariant its
  in
  let tdl = List.map build_type tdl in
  mk_decl (PDdata tdl) Sid.empty !news

let add_invariant pd its p =
  if not its.its_inv then invalid_arg "Mlw_decl.add_invariant";
  t_v_fold (fun _ vs -> raise (Decl.UnboundVar vs)) () p;
  let rec add = function
    | (s, cls, inv) :: tdl when its_equal s its ->
        check_post (t_type inv) p;
        let v, q = open_post inv in
        let u, p = open_post p in
        let q = t_and_simp (t_subst_single v (t_var u) q) p in
        let inv = create_post u q in
        (s, cls, inv) :: tdl
    | td :: tdl ->
        td :: add tdl
    | [] -> raise Not_found
  in
  match pd.pd_node with
    | PDdata tdl -> mk_decl (PDdata (add tdl)) pd.pd_syms pd.pd_news
    | _ -> invalid_arg "Mlw_decl.add_invariant"

let check_vars vars =
  if not (Stv.is_empty vars.vars_tv) then
    Loc.errorm "Type variable '%s cannot be generalized"
      (Stv.choose vars.vars_tv).tv_name.id_string

let letvar_news = function
  | LetV pv ->
    check_vars pv.pv_ity.ity_vars;
    Sreg.fold
      (fun r acc -> Sid.add r.reg_name acc)
      pv.pv_ity.ity_vars.vars_reg
      (Sid.singleton pv.pv_vs.vs_name)
  | LetA ps -> check_vars ps.ps_vars; Sid.singleton ps.ps_name

let ids_of_pvset s pvs =
  Spv.fold (fun pv s -> Sid.add pv.pv_vs.vs_name s) pvs s

let ids_of_syms s { syms_pv = pvs; syms_ps = pss } =
  Sps.fold (fun ps s -> Sid.add ps.ps_name s) pss (ids_of_pvset s pvs)

let create_let_decl ld =
  let news = letvar_news ld.let_sym in
  let syms = ids_of_syms Sid.empty ld.let_expr.e_syms in
  mk_decl (PDlet ld) syms news

let create_rec_decl fdl =
  let add_fd s { fun_ps = p } =
    check_vars p.ps_vars; news_id s p.ps_name in
  let news = List.fold_left add_fd Sid.empty fdl in
  let syms = ids_of_syms Sid.empty (e_rec fdl e_void).e_syms in
  mk_decl (PDrec fdl) syms news

let create_val_decl lv =
  let news = letvar_news lv in
  let syms = match lv with
    | LetA ps -> ids_of_pvset Sid.empty ps.ps_pvset
    | LetV _  -> Sid.empty in
  mk_decl (PDval lv) syms news

let create_exn_decl xs =
  let news = Sid.singleton xs.xs_name in
  mk_decl (PDexn xs) Sid.empty news

(** {2 Cloning} *)

let clone_data_decl sm pd = match pd.pd_node with
  | PDdata tdl ->
      let news = ref Sid.empty in
      let add_pl pl =
        let pl = Mls.find pl.pl_ls sm.sm_pls in
        news := news_id !news pl.pl_ls.ls_name;
        pl in
      let add_cs (cs,pjl) =
        add_pl cs, List.map (Opt.map add_pl) pjl in
      let add_td (its,csl,inv) =
        let conv_ts ts = Mts.find_def ts ts sm.sm_pure.Theory.sm_ts in
        let conv_ls ls = Mls.find_def ls ls sm.sm_pure.Theory.sm_ls in
        let inv = Term.t_s_map (Ty.ty_s_map conv_ts) conv_ls inv in
        let its = Mits.find its sm.sm_its in
        news := news_id !news its.its_ts.ts_name;
        its, List.map add_cs csl, inv in
      let tdl = List.map add_td tdl in
      mk_decl (PDdata tdl) Sid.empty !news
  | _ -> invalid_arg "Mlw_decl.clone_data_decl"

(** {2 Known identifiers} *)

type known_map = pdecl Mid.t

let known_id kn id =
  if not (Mid.mem id kn) then raise (UnknownIdent id)

let merge_known kn1 kn2 =
  let check_known id decl1 decl2 =
    if pd_equal decl1 decl2 then Some decl1
    else raise (RedeclaredIdent id)
  in
  Mid.union check_known kn1 kn2

let known_add_decl lkn0 kn0 d =
  let kn = Mid.map (Util.const d) d.pd_news in
  let check id decl0 _ =
    if pd_equal decl0 d
    then raise (KnownIdent id)
    else raise (RedeclaredIdent id) in
  let kn = Mid.union check kn0 kn in
  let unk = Mid.set_diff d.pd_syms kn in
  let unk = Mid.set_diff unk lkn0 in
  if Sid.is_empty unk then kn
  else raise (UnknownIdent (Sid.choose unk))

let rec find_td its1 = function
  | (its2,csl,inv) :: _ when its_equal its1 its2 -> csl,inv
  | _ :: tdl -> find_td its1 tdl
  | [] -> raise Not_found

let find_constructors kn its =
  match (Mid.find its.its_ts.ts_name kn).pd_node with
  | PDtype _ -> []
  | PDdata tdl -> fst (find_td its tdl)
  | PDval _ | PDlet _ | PDrec _ | PDexn _ -> assert false

let find_invariant kn its =
  match (Mid.find its.its_ts.ts_name kn).pd_node with
  | PDtype _ -> null_invariant its
  | PDdata tdl -> snd (find_td its tdl)
  | PDval _ | PDlet _ | PDrec _ | PDexn _ -> assert false

let rec find_def ps = function
  | d :: _ when ps_equal ps d.fun_ps -> d
  | _ :: l -> find_def ps l
  | [] -> raise Not_found

let find_definition kn ps =
  match (Mid.find ps.ps_name kn).pd_node with
  | PDtype _ -> assert false
  | PDdata _ -> assert false
  | PDval _ -> None
  | PDlet _ -> assert false
  | PDrec dl -> Some (find_def ps dl)
  | PDexn _ -> assert false

let check_match lkn _kn d =
  let rec checkE () e = match e.e_node with
    | Ecase (_,bl) ->
        let pl = List.map (fun (pp,_) -> [pp.ppat_pattern]) bl in
        let get_constructors s = List.map fst (Decl.find_constructors lkn s) in
        Loc.try2 ?loc:e.e_loc (Pattern.check_compile ~get_constructors) [] pl;
        e_fold checkE () e
    | _ -> e_fold checkE () e
  in
  match d.pd_node with
  | PDrec fdl -> List.iter (fun fd -> checkE () fd.fun_lambda.l_expr) fdl
  | PDlet { let_expr = e } -> checkE () e
  | PDval _ | PDtype _ | PDdata _ | PDexn _ -> ()

exception NonupdatableType of ity

let inst_constructors lkn kn ity = match ity.ity_node with
  | Itypur (ts,_) ->
      let csl = Decl.find_constructors lkn ts in
      let d = Mid.find ts.ts_name lkn in
      let is_rec = Mid.mem ts.ts_name d.Decl.d_syms in
      if csl = [] || is_rec then raise (NonupdatableType ity);
      let base = ity_pur ts (List.map ity_var ts.ts_args) in
      let sbs = ity_match ity_subst_empty base ity in
      let subst ty = {
        fd_ity   = ity_full_inst sbs (ity_of_ty ty);
        fd_ghost = false;
        fd_mut   = None; } in
      List.map (fun (cs,_) -> cs, List.map subst cs.ls_args) csl
  | Ityapp (its,_,_) ->
      let csl = find_constructors kn its in
      let d = Mid.find its.its_ts.ts_name lkn in
      let is_rec = Mid.mem its.its_ts.ts_name d.Decl.d_syms in
      if csl = [] || is_rec then raise (NonupdatableType ity);
      let args = List.map ity_var its.its_ts.ts_args in
      let base = ity_app its args its.its_regs in
      let sbs = ity_match ity_subst_empty base ity in
      let subst fd = {
        fd_ity   = ity_full_inst sbs fd.fd_ity;
        fd_ghost = fd.fd_ghost;
        fd_mut   = Opt.map (reg_full_inst sbs) fd.fd_mut; } in
      List.map (fun (cs,_) -> cs.pl_ls, List.map subst cs.pl_args) csl
  | Ityvar _ ->
      invalid_arg "Mlw_decl.inst_constructors"

let known_add_decl lkn kn d =
  let kn = known_add_decl lkn kn d in
  check_match lkn kn d;
  kn

