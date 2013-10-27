(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2013   --   INRIA - CNRS - Paris-Sud University  *)
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
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

(** Program types *)

type dity =
  | Dvar of dvar ref
  | Dutv of tvsymbol
  | Dapp of itysymbol * dity list * dreg list
  | Dpur of tysymbol  * dity list

and dvar =
  | Dtvs of tvsymbol
  | Dval of dity

and dreg =
  | Rreg of region * dity
  | Rvar of rvar ref

and rvar =
  | Rtvs of tvsymbol * dity
  | Rval of dreg

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)

let create_dreg dity =
  Rvar (ref (Rtvs (create_tvsymbol (id_fresh "rho"), dity)))

let dity_of_ity ity =
  let hreg = Hreg.create 3 in
  let rec dity ity = match ity.ity_node with
    | Ityvar tv -> Dutv tv
    | Ityapp (s,tl,rl) -> Dapp (s, List.map dity tl, List.map dreg rl)
    | Itypur (s,tl)    -> Dpur (s, List.map dity tl)
  and dreg reg =
    try Hreg.find hreg reg with Not_found ->
    let r = create_dreg (dity reg.reg_ity) in
    Hreg.add hreg reg r;
    r
  in
  dity ity

let ity_of_dity dity =
  let rec ity = function
    | Dvar { contents = Dval t } -> ity t
    | Dvar ref ->
        let tv = create_tvsymbol (id_fresh "xi") in
        ref := Dval (Dutv tv);
        ity_var tv
    | Dutv tv -> ity_var tv
    | Dapp (s,tl,rl) -> ity_app s (List.map ity tl) (List.map reg rl)
    | Dpur (s,tl)    -> ity_pur s (List.map ity tl)
  and reg = function
    | Rreg (r,_) -> r
    | Rvar { contents = Rval r } -> reg r
    | Rvar ({ contents = Rtvs (tv,t) } as ref) ->
        let r = create_region (id_clone tv.tv_name) (ity t) in
        ref := Rval (Rreg (r,t));
        r
  in
  ity dity

let dity_int  = Dpur (ts_int,  [])
let dity_real = Dpur (ts_real, [])
let dity_bool = Dpur (ts_bool, [])
let dity_unit = Dpur (ts_unit, [])

(** Destructive type unification *)

let rec occur_check tv = function
  | Dvar { contents = Dval d } -> occur_check tv d
  | Dapp (_,dl,_) | Dpur (_,dl) -> List.iter (occur_check tv) dl
  | Dvar { contents = Dtvs tv' } | Dutv tv' ->
      if tv_equal tv tv' then raise Exit

let rec dity_unify d1 d2 = match d1,d2 with
  | Dvar { contents = Dval d1 }, d2
  | d1, Dvar { contents = Dval d2 } ->
      dity_unify d1 d2
  | Dvar { contents = Dtvs tv1 },
    Dvar { contents = Dtvs tv2 } when tv_equal tv1 tv2 ->
      ()
  | Dvar ({ contents = Dtvs tv } as r), d
  | d, Dvar ({ contents = Dtvs tv } as r) ->
      occur_check tv d;
      r := Dval d
  | Dutv tv1, Dutv tv2 when tv_equal tv1 tv2 ->
      ()
  | Dapp (s1,dl1,_), Dapp (s2,dl2,_) when its_equal s1 s2 ->
      List.iter2 dity_unify dl1 dl2
  | Dpur (s1,dl1), Dpur (s2,dl2) when ts_equal s1 s2 ->
      List.iter2 dity_unify dl1 dl2
  | _ -> raise Exit

(** Reunify regions *)

let dtvs_queue : dvar ref Queue.t = Queue.create ()

let unify_queue : (dity * dity) Queue.t = Queue.create ()

let dity_fresh () =
  let r = ref (Dtvs (create_tvsymbol (id_fresh "a"))) in
  Queue.add r dtvs_queue;
  Dvar r

let its_app_fresh s dl =
  let htv = Htv.create 3 in
  let hreg = Hreg.create 3 in
  let rec inst ity = match ity.ity_node with
    | Ityvar v -> Htv.find htv v
    | Ityapp (s,tl,rl) -> Dapp (s, List.map inst tl, List.map fresh rl)
    | Itypur (s,tl)    -> Dpur (s, List.map inst tl)
  and fresh r =
    try Hreg.find hreg r with Not_found ->
    let reg = create_dreg (inst r.reg_ity) in
    Hreg.add hreg r reg;
    reg in
  List.iter2 (Htv.add htv) s.its_ts.ts_args dl;
  match s.its_def with
  | None -> Dapp (s, dl, List.map fresh s.its_regs)
  | Some ity -> inst ity

let rec dity_refresh = function
  | Dvar { contents = Dval dty } -> dity_refresh dty
  | Dvar { contents = Dtvs _ } as dity -> dity
  | Dapp (s,dl,_) -> its_app_fresh s (List.map dity_refresh dl)
  | Dpur (s,dl) -> Dpur (s, List.map dity_refresh dl)
  | Dutv _ as dity -> dity

let dity_unify_weak = dity_unify

let dity_unify d1 d2 = dity_unify d1 d2; Queue.add (d1,d2) unify_queue

let rec reunify d1 d2 = match d1,d2 with
  | Dvar { contents = Dval d1 }, d2
  | d1, Dvar { contents = Dval d2 } -> reunify d1 d2
  | Dvar _, Dvar _ | Dutv _, Dutv _ -> ()
  | Dapp (_,dl1,rl1), Dapp (_,dl2,rl2) ->
      List.iter2 reunify dl1 dl2;
      List.iter2 unify_reg rl1 rl2
  | Dpur (_,dl1), Dpur (_,dl2) ->
      List.iter2 reunify dl1 dl2
  | _ -> assert false

and unify_reg r1 r2 = match r1,r2 with
  | Rvar { contents = Rval r1 }, r2
  | r1, Rvar { contents = Rval r2 } ->
      unify_reg r1 r2
  | Rvar { contents = Rtvs (tv1,_) },
    Rvar { contents = Rtvs (tv2,_) } when tv_equal tv1 tv2 ->
      ()
  | Rvar ({ contents = Rtvs (_,d1) } as r),
    (Rvar { contents = Rtvs (_,d2) } as d)
  | Rvar ({ contents = Rtvs (_,d1) } as r), (Rreg (_,d2) as d)
  | (Rreg (_,d1) as d), Rvar ({ contents = Rtvs (_,d2) } as r) ->
      reunify d1 d2;
      r := Rval d
  | Rreg _, Rreg _ -> ()
    (* we don't check whether the regions are the same,
       because we won't have a good location for the error.
       Let the core API raise the exception later. *)

let reunify_regions () =
  Queue.iter (fun r -> match !r with
    | Dval d -> r := Dval (dity_refresh d)
    | Dtvs _ -> ()) dtvs_queue;
  Queue.clear dtvs_queue;
  Queue.iter (fun (d1,d2) -> reunify d1 d2) unify_queue;
  Queue.clear unify_queue

(** Chainable relations *)

let rec dity_is_bool = function
  | Dvar { contents = Dval dty } -> dity_is_bool dty
  | Dpur (ts,_) -> ts_equal ts ts_bool
  | _ -> false

let dvty_is_chainable = function
  | [t1;t2],t ->
      dity_is_bool t && not (dity_is_bool t1) && not (dity_is_bool t2)
  | _ -> false

(** Pretty-printing *)

let debug_print_reg_types = Debug.register_info_flag "print_reg_types"
  ~desc:"Print@ types@ of@ regions@ (mutable@ fields)."

let print_dity fmt dity =
  let protect_on x s = if x then "(" ^^ s ^^ ")" else s in
  let print_rtvs fmt tv = Mlw_pretty.print_reg fmt
    (create_region (id_clone tv.tv_name) Mlw_ty.ity_unit) in
  let rec print_dity inn fmt = function
    | Dvar { contents = Dtvs tv }
    | Dutv tv -> Pretty.print_tv fmt tv
    | Dvar { contents = Dval dty } -> print_dity inn fmt dty
    | Dpur (s,tl) when is_ts_tuple s -> Format.fprintf fmt "(%a)"
        (Pp.print_list Pp.comma (print_dity false)) tl
    | Dpur (s,[]) -> Pretty.print_ts fmt s
    | Dpur (s,tl) -> Format.fprintf fmt (protect_on inn "%a@ %a")
        Pretty.print_ts s (Pp.print_list Pp.space (print_dity true)) tl
    | Dapp (s,[],rl) -> Format.fprintf fmt (protect_on inn "%a@ <%a>")
        Mlw_pretty.print_its s (Pp.print_list Pp.comma print_dreg) rl
    | Dapp (s,tl,rl) -> Format.fprintf fmt (protect_on inn "%a@ <%a>@ %a")
        Mlw_pretty.print_its s (Pp.print_list Pp.comma print_dreg) rl
          (Pp.print_list Pp.space (print_dity true)) tl
  and print_dreg fmt = function
    | Rreg (r,_) when Debug.test_flag debug_print_reg_types ->
        Format.fprintf fmt "@[%a:@,%a@]" Mlw_pretty.print_reg r
          Mlw_pretty.print_ity r.reg_ity
    | Rreg (r,_) -> Mlw_pretty.print_reg fmt r
    | Rvar { contents = Rtvs (tv,dity) }
      when Debug.test_flag debug_print_reg_types ->
        Format.fprintf fmt "@[%a:@,%a@]" print_rtvs tv (print_dity false) dity
    | Rvar { contents = Rtvs (tv,_) } -> print_rtvs fmt tv
    | Rvar { contents = Rval dreg } -> print_dreg fmt dreg
  in
  print_dity false fmt dity

(* Specialization of symbols *)

let specialize_scheme tvs (argl,res) =
  let htv = Htv.create 3 and hreg = Htv.create 3 in
  let rec spec_dity = function
    | Dvar { contents = Dval dity } -> spec_dity dity
    | Dvar { contents = Dtvs tv } | Dutv tv as dity -> get_tv tv dity
    | Dapp (s,dl,rl) -> Dapp (s, List.map spec_dity dl, List.map spec_reg rl)
    | Dpur (s,dl)    -> Dpur (s, List.map spec_dity dl)
  and spec_reg = function
    | Rvar { contents = Rval r } -> spec_reg r
    | Rvar { contents = Rtvs (tv,dity) } -> get_reg tv dity
    | Rreg _ as r -> r
  and get_tv tv dity = try Htv.find htv tv with Not_found ->
    let v = dity_fresh () in
    (* can't return dity, might differ in regions *)
    if Stv.mem tv tvs then dity_unify_weak v dity;
    Htv.add htv tv v;
    v
  and get_reg tv dity = try Htv.find hreg tv with Not_found ->
    let r = create_dreg (spec_dity dity) in
    Htv.add hreg tv r;
    r in
  List.map spec_dity argl, spec_dity res

let spec_ity htv hreg vars ity =
  let get_tv tv =
    try Htv.find htv tv with Not_found ->
    let v = dity_fresh () in
    Htv.add htv tv v;
    v in
  let rec dity ity = match ity.ity_node with
    | Ityvar tv -> if Stv.mem tv vars.vars_tv then Dutv tv else get_tv tv
    | Ityapp (s,tl,rl) -> Dapp (s, List.map dity tl, List.map dreg rl)
    | Itypur (s,tl)    -> Dpur (s, List.map dity tl)
  and dreg reg = try Hreg.find hreg reg with Not_found ->
    let t = dity reg.reg_ity in
    let r = if reg_occurs reg vars then Rreg (reg,t) else create_dreg t in
    Hreg.add hreg reg r;
    r
  in
  dity ity

let specialize_pv { pv_ity = ity } =
  spec_ity (Htv.create 3) (Hreg.create 3) ity.ity_vars ity

let specialize_xs { xs_ity = ity } =
  spec_ity (Htv.create 3) (Hreg.create 3) ity.ity_vars ity

let specialize_ps { ps_aty = aty; ps_vars = vars } =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  let conv pv = spec_ity htv hreg vars pv.pv_ity in
  let rec spec_aty a =
    let argl = List.map conv a.aty_args in
    let narg,res = match a.aty_result with
      | VTvalue v -> [], spec_ity htv hreg vars v
      | VTarrow a -> spec_aty a in
    argl @ narg, res in
  spec_aty aty

let specialize_pl pl =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  let conv fd = spec_ity htv hreg vars_empty fd.fd_ity in
  List.map conv pl.pl_args, conv pl.pl_value

let dity_of_ty htv hreg vars ty =
  let rec pure ty = match ty.ty_node with
    | Tyapp (ts,tl) ->
        begin try ignore (restore_its ts); false
        with Not_found -> List.for_all pure tl end
    | Tyvar _ -> true in
  if not (pure ty) then raise Exit;
  spec_ity htv hreg vars (ity_of_ty ty)

let specialize_ls ls =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  let conv ty = dity_of_ty htv hreg vars_empty ty in
  let ty = Opt.get_def ty_bool ls.ls_value in
  List.map conv ls.ls_args, conv ty

let specialize_ls ls =
  try specialize_ls ls with Exit ->
    Loc.errorm "Function symbol `%a' can only be used in specification"
      Pretty.print_ls ls

(** Patterns *)

type dpattern = {
  dp_pat  : pre_ppattern;
  dp_dity : dity;
  dp_vars : dity Mstr.t;
  dp_loc  : Loc.position option;
}

type dpattern_node =
  | DPwild
  | DPvar  of preid
  | DPlapp of lsymbol * dpattern list
  | DPpapp of plsymbol * dpattern list
  | DPor   of dpattern * dpattern
  | DPas   of dpattern * preid

(** Specifications *)

type ghost = bool

type opaque = Stv.t

type dbinder = preid option * ghost * opaque * dity

type 'a later = vsymbol Mstr.t -> 'a
  (* specification terms are parsed and typechecked after the program
     expressions, when the types of locally bound program variables are
     already established. *)

type dspec = {
  ds_pre     : pre;
  ds_post    : post;
  ds_xpost   : xpost;
  ds_reads   : vsymbol list;
  ds_writes  : term list;
  ds_variant : variant list;
}

type dtype_v =
  | DSpecV of dity
  | DSpecA of dbinder list * dtype_c

and dtype_c = dtype_v * dspec later

(** Expressions *)

type dlazy_op = DEand | DEor

type dexpr = {
  de_node : dexpr_node;
  de_dvty : dvty;
  de_loc  : Loc.position option;
}

and dexpr_node =
  | DEvar of string * dvty
  | DEgpvar of pvsymbol
  | DEgpsym of psymbol
  | DEplapp of plsymbol * dexpr list
  | DElsapp of lsymbol * dexpr list
  | DEapply of dexpr * dexpr list
  | DEconst of Number.constant
  | DEval of dval_decl * dexpr
  | DElet of dlet_defn * dexpr
  | DEfun of dfun_defn * dexpr
  | DErec of dfun_defn list * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEmatch of dexpr * (dpattern * dexpr) list
  | DEassign of plsymbol * dexpr * dexpr
  | DElazy of dlazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEtrue
  | DEfalse
  | DEraise of xsymbol * dexpr
  | DEtry of dexpr * (xsymbol * dpattern * dexpr) list
  | DEfor of preid * dexpr * for_direction * dexpr * invariant later * dexpr
  | DEloop of variant list later * invariant later * dexpr
  | DEabsurd
  | DEassert of assertion_kind * term later
  | DEabstract of dexpr * dspec later
  | DEmark of preid * dexpr
  | DEghost of dexpr
  | DEany of dtype_c
  | DEcast of dexpr * ity
  | DEuloc of dexpr * Loc.position
  | DElabel of dexpr * Slab.t

and dval_decl = preid * ghost * dtype_v

and dlet_defn = preid * ghost * dexpr

and dfun_defn = preid * ghost * dbinder list * dexpr * dspec later

(** Environment *)

type denv = {
  frozen : dity list;
  locals : (Stv.t option * dvty) Mstr.t;
}

let denv_empty = { frozen = []; locals = Mstr.empty }

let is_frozen frozen tv =
  try List.iter (occur_check tv) frozen; false with Exit -> true

let freeze_dvty frozen (argl,res) =
  let rec add l = function
    | Dvar { contents = Dval d } -> add l d
    | Dvar { contents = Dtvs _ } as d -> d :: l
    | Dutv _ as d -> d :: l
    | Dapp (_,tl,_) | Dpur (_,tl) -> List.fold_left add l tl in
  List.fold_left add (add frozen res) argl

let free_vars frozen (argl,res) =
  let rec add s = function
    | Dvar { contents = Dval d } -> add s d
    | Dvar { contents = Dtvs tv }
    | Dutv tv -> if is_frozen frozen tv then s else Stv.add tv s
    | Dapp (_,tl,_) | Dpur (_,tl) -> List.fold_left add s tl in
  List.fold_left add (add Stv.empty res) argl

let denv_add_mono { frozen = frozen; locals = locals } id dvty =
  let locals = Mstr.add id.pre_name (None, dvty) locals in
  { frozen = freeze_dvty frozen dvty; locals = locals }

let denv_add_poly { frozen = frozen; locals = locals } id dvty =
  let ftvs = free_vars frozen dvty in
  let locals = Mstr.add id.pre_name (Some ftvs, dvty) locals in
  { frozen = frozen; locals = locals }

let denv_add_rec_mono { frozen = frozen; locals = locals } id dvty =
  let locals = Mstr.add id.pre_name (Some Stv.empty, dvty) locals in
  { frozen = freeze_dvty frozen dvty; locals = locals }

let denv_add_rec_poly { frozen = frozen; locals = locals } frozen0 id dvty =
  let ftvs = free_vars frozen0 dvty in
  let locals = Mstr.add id.pre_name (Some ftvs, dvty) locals in
  { frozen = frozen; locals = locals }

let denv_add_rec denv frozen0 id ((argl,res) as dvty) =
  let rec is_explicit = function
    | Dapp (_,tl,_) | Dpur (_,tl) -> List.for_all is_explicit tl
    | Dvar { contents = Dval d } -> is_explicit d
    | Dvar { contents = Dtvs _ } -> false
    | Dutv _ -> true in
  if List.for_all is_explicit argl && is_explicit res
  then denv_add_rec_poly denv frozen0 id dvty
  else denv_add_rec_mono denv id dvty

let dvty_of_dtype_v dtv =
  let rec dvty argl = function
    | DSpecA (bl,(DSpecV res,_)) ->
        List.rev_append argl (List.map (fun (_,_,_,t) -> t) bl), res
    | DSpecA (bl,(dtv,_)) ->
        dvty (List.fold_left (fun l (_,_,_,t) -> t::l) argl bl) dtv
    | DSpecV res -> List.rev argl, res in
  dvty [] dtv

let denv_add_val denv (id,_,dtv) =
  denv_add_poly denv id (dvty_of_dtype_v dtv)

let denv_add_let denv (id,_,{de_dvty = dvty}) =
  denv_add_mono denv id dvty

let denv_add_fun denv (id,_,bl,{de_dvty = (argl,res)},_) =
  let argl = List.fold_right (fun (_,_,_,t) l -> t::l) bl argl in
  denv_add_poly denv id (argl, res)

exception DupId of preid

let denv_prepare_rec denv0 l =
  let add s (id,_,_) =
    Sstr.add_new (DupId id) id.pre_name s in
  let _ = try List.fold_left add Sstr.empty l
    with DupId id -> Loc.errorm ?loc:id.pre_loc
      "duplicate function name %s" id.pre_name in
  let add denv (id,bl,res) =
    let argl = List.map (fun (_,_,_,t) -> t) bl in
    denv_add_rec denv denv0.frozen id (argl,res) in
  List.fold_left add denv0 l

let denv_verify_rec { frozen = frozen; locals = locals } id =
  let check tv = if is_frozen frozen tv then Loc.errorm ?loc:id.pre_loc
    "This function is expected to be polymorphic in type variable %a"
    Pretty.print_tv tv in
  match Mstr.find_opt id.pre_name locals with
    | Some (Some tvs, _) -> Stv.iter check tvs
    | Some (None, _) -> assert false
    | None -> assert false

let denv_add_args { frozen = frozen; locals = locals } bl =
  let l = List.fold_left (fun l (_,_,_,t) -> t::l) frozen bl in
  let add s (id,_,_,t) = match id with
    | Some {pre_name = n} ->
        Mstr.add_new (Dterm.DuplicateVar n) n (None, ([],t)) s
    | None -> s in
  let s = List.fold_left add Mstr.empty bl in
  { frozen = l; locals = Mstr.set_union s locals }

let denv_add_pat { frozen = frozen; locals = locals } dp =
  let l = Mstr.fold (fun _ t l -> t::l) dp.dp_vars frozen in
  let s = Mstr.map (fun t -> None, ([], t)) dp.dp_vars in
  { frozen = l; locals = Mstr.set_union s locals }

let mk_node n = function
  | Some tvs, dvty -> DEvar (n, specialize_scheme tvs dvty)
  | None,     dvty -> DEvar (n, dvty)

let denv_get denv n =
  mk_node n (Mstr.find_exn (Dterm.UnboundVar n) n denv.locals)

let denv_get_opt denv n =
  Opt.map (mk_node n) (Mstr.find_opt n denv.locals)

(** Unification tools *)

let dity_unify_app ls fn l1 l2 =
  try List.iter2 fn l1 l2 with Invalid_argument _ ->
    raise (BadArity (ls, List.length l2))

let dpat_expected_type {dp_dity = dp_dity; dp_loc = loc} dity =
  try dity_unify dp_dity dity with Exit -> Loc.errorm ?loc
    "This pattern has type %a,@ but is expected to have type %a"
    print_dity dp_dity print_dity dity

let dexpr_expected_type {de_dvty = (al,res); de_loc = loc} dity =
  if al <> [] then Loc.errorm ?loc "This expression is not a first-order value";
  try dity_unify res dity with Exit -> Loc.errorm ?loc
    "This expression has type %a,@ but is expected to have type %a"
    print_dity res print_dity dity

let dexpr_expected_type_weak {de_dvty = (al,res); de_loc = loc} dity =
  if al <> [] then Loc.errorm ?loc "This expression is not a first-order value";
  try dity_unify_weak res dity with Exit -> Loc.errorm ?loc
    "This expression has type %a,@ but is expected to have type %a"
    print_dity res print_dity dity

(** Constructors *)

let dpattern ?loc node =
  let mk_dpat pre dity vars =
    { dp_pat = pre; dp_dity = dity; dp_vars = vars; dp_loc = loc } in
  let dpat = function
    | DPwild ->
        mk_dpat PPwild (dity_fresh ()) Mstr.empty
    | DPvar id ->
        let dity = dity_fresh () in
        mk_dpat (PPvar id) dity (Mstr.singleton id.pre_name dity)
    | DPlapp (ls,dpl) ->
        if ls.ls_constr = 0 then raise (ConstructorExpected ls);
        let argl, res = specialize_ls ls in
        dity_unify_app ls dpat_expected_type dpl argl;
        let join n _ _ = raise (Dterm.DuplicateVar n) in
        let add acc dp = Mstr.union join acc dp.dp_vars in
        let vars = List.fold_left add Mstr.empty dpl in
        let ppl = List.map (fun dp -> dp.dp_pat) dpl in
        mk_dpat (PPlapp (ls, ppl)) res vars
    | DPpapp ({pl_ls = ls} as pl, dpl) ->
        if ls.ls_constr = 0 then raise (ConstructorExpected ls);
        let argl, res = specialize_pl pl in
        dity_unify_app ls dpat_expected_type dpl argl;
        let join n _ _ = raise (Dterm.DuplicateVar n) in
        let add acc dp = Mstr.union join acc dp.dp_vars in
        let vars = List.fold_left add Mstr.empty dpl in
        let ppl = List.map (fun dp -> dp.dp_pat) dpl in
        mk_dpat (PPpapp (pl, ppl)) res vars
    | DPor (dp1,dp2) ->
        dpat_expected_type dp2 dp1.dp_dity;
        let join n dity1 dity2 = try dity_unify dity1 dity2; Some dity1
          with Exit -> Loc.errorm ?loc
            "Variable %s has type %a,@ but is expected to have type %a"
            n print_dity dity1 print_dity dity2 in
        let vars = Mstr.union join dp1.dp_vars dp2.dp_vars in
        mk_dpat (PPor (dp1.dp_pat, dp2.dp_pat)) dp1.dp_dity vars
    | DPas (dp, ({pre_name = n} as id)) ->
        let { dp_pat = pat; dp_dity = dity; dp_vars = vars } = dp in
        let vars = Mstr.add_new (Dterm.DuplicateVar n) n dity vars in
        mk_dpat (PPas (pat, id)) dity vars
  in
  Loc.try1 ?loc dpat node

let dexpr ?loc node =
  let get_dvty = function
    | DEvar (_,dvty) ->
        dvty
    | DEgpvar pv ->
        [], specialize_pv pv
    | DEgpsym ps ->
        specialize_ps ps
    | DEplapp (pl,del) ->
        let argl, res = specialize_pl pl in
        dity_unify_app pl.pl_ls dexpr_expected_type del argl;
        [], res
    | DElsapp (ls,del) ->
        let argl, res = specialize_ls ls in
        dity_unify_app ls dexpr_expected_type del argl;
        [], res
    | DEapply (de,del) ->
        let argl, res = de.de_dvty in
        let rec down del al = match del, al with
          | de::del, dity::al -> dexpr_expected_type de dity; down del al
          | [], _ -> al
          | _ when argl = [] -> Loc.errorm
              "This expression is not a function and cannot be applied"
          | _ -> Loc.errorm
              "This function is applied to too many arguments" in
        down del argl, res
    | DEconst (Number.ConstInt _) ->
        [], dity_int
    | DEconst (Number.ConstReal _) ->
        [], dity_real
    | DEval (_,de)
    | DElet (_,de)
    | DEfun (_,de)
    | DErec (_,de) ->
        de.de_dvty
    | DEif (de1,de2,de3) ->
        let res = dity_fresh () in
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 res;
        dexpr_expected_type de3 res;
        de2.de_dvty
    | DEmatch (de,bl) ->
        let ety = dity_fresh () in
        let res = dity_fresh () in
        dexpr_expected_type de ety;
        let branch (dp,de) =
          dpat_expected_type dp ety;
          dexpr_expected_type de res in
        List.iter branch bl;
        [], res
    | DEassign (pl,de1,de2) ->
        let argl, res = specialize_pl pl in
        dity_unify_app pl.pl_ls dexpr_expected_type [de1] argl;
        dexpr_expected_type_weak de2 res;
        [], dity_unit
    | DElazy (_,de1,de2) ->
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 dity_bool;
        de1.de_dvty
    | DEnot de ->
        dexpr_expected_type de dity_bool;
        de.de_dvty
    | DEtrue
    | DEfalse ->
        [], dity_bool
    | DEraise (xs,de) ->
        dexpr_expected_type de (specialize_xs xs);
        [], dity_fresh ()
    | DEtry (de,bl) ->
        let res = dity_fresh () in
        dexpr_expected_type de res;
        let branch (xs,dp,de) =
          let ety = specialize_xs xs in
          dpat_expected_type dp ety;
          dexpr_expected_type de res in
        List.iter branch bl;
        de.de_dvty
    | DEfor (_,de_from,_,de_to,_,de) ->
        dexpr_expected_type de_from dity_int;
        dexpr_expected_type de_to dity_int;
        dexpr_expected_type de dity_unit;
        de.de_dvty
    | DEloop (_,_,de) ->
        dexpr_expected_type de dity_unit;
        de.de_dvty
    | DEabsurd ->
        [], dity_fresh ()
    | DEassert _ ->
        [], dity_unit
    | DEabstract (de,_)
    | DEmark (_,de)
    | DEghost de ->
        de.de_dvty
    | DEany (dtv,_) ->
        dvty_of_dtype_v dtv
    | DEcast (de,ity) ->
        dexpr_expected_type_weak de (dity_of_ity ity);
        de.de_dvty
    | DEuloc (de,_)
    | DElabel (de,_) ->
        de.de_dvty in
  let dvty = Loc.try1 ?loc get_dvty node in
  { de_node = node; de_dvty = dvty; de_loc = loc }

(** Specifications *)

let check_at f0 =
  let rec check f = match f.t_node with
    | Term.Tapp (ls, _) when ls_equal ls Mlw_wp.fs_at ->
        let d = Mvs.set_diff f.t_vars f0.t_vars in
        Mvs.is_empty d || Loc.errorm ?loc:f.t_loc
          "locally bound variable %a under `at'"
          Pretty.print_vs (fst (Mvs.choose d))
    | _ ->
        t_all check f
  in
  ignore (check f0)

let get_variant vsm (vl : variant list later) =
  let vl = vl vsm in
  List.iter (fun (t,_) -> check_at t) vl;
  vl

let get_assert vsm (f : term later) =
  let f = f vsm in
  check_at f;
  f

(** Final stage *)

type local_env = {
  psm : psymbol Mstr.t;
  pvm : pvsymbol Mstr.t;
  vsm : vsymbol Mstr.t;
}

let env_empty = {
  psm = Mstr.empty;
  pvm = Mstr.empty;
  vsm = Mstr.empty;
}

let add_let_sym {psm = psm; pvm = pvm; vsm = vsm} {pre_name = n} = function
  | LetV pv ->
      { psm = psm; pvm = Mstr.add n pv pvm; vsm = Mstr.add n pv.pv_vs vsm }
  | LetA ps ->
      { psm = Mstr.add n ps psm; pvm = pvm; vsm = vsm }

let add_pv_map {psm = psm; pvm = pvm; vsm = vsm} vm =
  let um = Mstr.map (fun pv -> pv.pv_vs) vm in
  { psm = psm; pvm = Mstr.set_union vm pvm; vsm = Mstr.set_union um vsm }

let e_ghostify gh e =
  if gh && not e.e_ghost then e_ghost e else e

let expr ~keep_loc de =
  reunify_regions (); (* no more unifications *)

  let rec strip uloc labs de = match de.de_node with
    | DEcast (de,_) -> strip uloc labs de
    | DEuloc (de,loc) -> strip (Some loc) labs de
    | DElabel (de,s) -> strip uloc (Slab.union labs s) de
    | _ -> uloc, labs, de in

  let rec get uloc env ({ de_loc = loc } as de) =
    let uloc, labs, de = strip uloc Slab.empty de in
    let e = Loc.try4 ?loc try_get uloc env de.de_dvty de.de_node in
    let loc = if keep_loc then loc else None in
    let loc = if uloc <> None then uloc else loc in
    if loc = None && Slab.is_empty labs then e else
    e_label ?loc labs e

  and try_get uloc env (argl,res) = function
    | DEvar (n,_) when argl = [] ->
        e_value (Mstr.find_exn (Dterm.UnboundVar n) n env.pvm)
    | DEvar (n,_) ->
        let ps = Mstr.find_exn (Dterm.UnboundVar n) n env.psm in
        e_arrow ps (List.map ity_of_dity argl) (ity_of_dity res)
    | DEgpvar pv ->
        e_value pv
    | DEgpsym ps ->
        e_arrow ps (List.map ity_of_dity argl) (ity_of_dity res)
    | DEplapp (pl,del) ->
        let get_gh fd de = e_ghostify fd.fd_ghost (get uloc env de) in
        e_plapp pl (List.map2 get_gh pl.pl_args del) (ity_of_dity res)
    | DElsapp (ls,del) ->
        e_lapp ls (List.map (get uloc env) del) (ity_of_dity res)
    | DEapply (de,del) ->
        let rec ghostify_args del = function
          | VTvalue _ -> assert (del = []); []
          | VTarrow a ->
              let rec args del al = match del, al with
                | de::del, {pv_ghost = gh}::al ->
                    e_ghostify gh (get uloc env de) :: args del al
                | [], _ -> []
                | _, [] -> ghostify_args del a.aty_result in
              args del a.aty_args in
        let e = get uloc env de in
        e_app e (ghostify_args del e.e_vty)
    | DEconst c ->
        e_const c
    | DEval ((_id,_gh,_dtv),_de) ->
        assert false (* TODO *)
    | DElet ((id,gh,de1),de2) ->
        let e1 = get uloc env de1 in
        let mk_expr e1 =
          let e1 = e_ghostify gh e1 in
          let ld1 = create_let_defn id e1 in
          let env = add_let_sym env id ld1.let_sym in
          let e2 = get uloc env de2 in
          let e2_unit = match e2.e_vty with
            | VTvalue ity -> ity_equal ity ity_unit
            | _ -> false in
          let e1_no_eff =
            Sreg.is_empty e1.e_effect.eff_writes &&
            Sexn.is_empty e1.e_effect.eff_raises &&
            not e1.e_effect.eff_diverg in
          let e2 =
            if e2_unit (* e2 is unit *)
              && e2.e_ghost (* and e2 is ghost *)
              && not e1.e_ghost (* and e1 is non-ghost *)
              && not e1_no_eff (* and e1 has observable effects *)
            then e_let (create_let_defn (id_fresh "gh") e2) e_void
            else e2 in
          e_let ld1 e2 in
        let rec flatten e1 = match e1.e_node with
          | Elet (ld,_) (* can't let a non-ghost expr escape *)
            when gh && not ld.let_expr.e_ghost -> mk_expr e1
          | Elet (ld,e1) -> e_let ld (flatten e1)
          | _ -> mk_expr e1 in
        begin match e1.e_vty with
          | VTarrow _ when e1.e_ghost && not gh ->
              Loc.errorm "%s must be a ghost function" id.pre_name
          | VTarrow _ -> flatten e1
          | VTvalue _ -> mk_expr e1
        end
(*
    | DEfun (_,de)
    | DErec (_,de) ->
        de.de_dvty
*)
    | DEif (de1,de2,de3) ->
        let e1 = get uloc env de1 in
        let e2 = get uloc env de2 in
        let e3 = get uloc env de3 in
        e_if e1 e2 e3
    | DEmatch (de1,bl) ->
        let e1 = get uloc env de1 in
        let ity = ity_of_expr e1 in
        let ghost = e1.e_ghost in
        let branch (dp,de) =
          let vm, pat = make_ppattern dp.dp_pat ~ghost ity in
          pat, get uloc (add_pv_map env vm) de in
        e_case e1 (List.map branch bl)
    | DEassign (pl,de1,de2) ->
        e_assign pl (get uloc env de1) (get uloc env de2)
    | DElazy (DEand,de1,de2) ->
        e_lazy_and (get uloc env de1) (get uloc env de2)
    | DElazy (DEor,de1,de2) ->
        e_lazy_or (get uloc env de1) (get uloc env de2)
    | DEnot de ->
        e_not (get uloc env de)
    | DEtrue ->
        e_true
    | DEfalse ->
        e_false
    | DEraise (xs,de) ->
        e_raise xs (get uloc env de) (ity_of_dity res)
    | DEtry (de1,bl) ->
        let e1 = get uloc env de1 in
        let add_branch (m,l) (xs,dp,de) =
          let vm, pat = make_ppattern dp.dp_pat xs.xs_ity in
          let e = get uloc (add_pv_map env vm) de in
          try Mexn.add xs ((pat,e) :: Mexn.find xs m) m, l
          with Not_found -> Mexn.add xs [pat,e] m, (xs::l) in
        let xsm, xsl = List.fold_left add_branch (Mexn.empty,[]) bl in
        let mk_branch xs = match Mexn.find xs xsm with
          | [{ ppat_pattern = { pat_node = Pvar vs }}, e] ->
              xs, Mlw_ty.restore_pv vs, e
          | [{ ppat_pattern = { pat_node = Pwild }}, e] ->
              xs, create_pvsymbol (id_fresh "_") xs.xs_ity, e
          | [{ ppat_pattern = { pat_node = Papp (fs,[]) }}, e]
            when ls_equal fs Mlw_expr.fs_void ->
              xs, create_pvsymbol (id_fresh "_") xs.xs_ity, e
          | bl ->
              let pv = create_pvsymbol (id_fresh "res") xs.xs_ity in
              let bl = try
                let conv (p,_) = [p.ppat_pattern], t_void in
                let comp = Pattern.CompileTerm.compile_bare in
                ignore (comp [t_var pv.pv_vs] (List.rev_map conv bl));
                bl
              with Pattern.NonExhaustive _ ->
                let _, pp = make_ppattern PPwild pv.pv_ity in
                (pp, e_raise xs (e_value pv) (ity_of_dity res)) :: bl
              in
              xs, pv, e_case (e_value pv) (List.rev bl)
        in
        e_try e1 (List.rev_map mk_branch xsl)
(*
    | DEfor (_,de_from,_,de_to,_,de) ->
        dexpr_expected_type de_from dity_int;
        dexpr_expected_type de_to dity_int;
        dexpr_expected_type de dity_unit;
        de.de_dvty
    | DEloop (_,_,de) ->
        dexpr_expected_type de dity_unit;
        de.de_dvty
*)
    | DEabsurd ->
        e_absurd (ity_of_dity res)
    | DEassert (ak,f) ->
        e_assert ak (get_assert env.vsm f)
(*
    | DEabstract (de,_)
*)
    | DEmark (id,de) ->
        let ld = create_let_defn id Mlw_wp.e_now in
        let env = add_let_sym env id ld.let_sym in
        e_let ld (get uloc env de)
    | DEghost de ->
        (* keep user ghost annotations even if redundant *)
        e_ghost (get uloc env de)
(*
    | DEany (dtv,_) ->
        dvty_of_dtype_v dtv
*)
    | DEcast _ | DEuloc _ | DElabel _ ->
        assert false (* already stripped *)
  in
  get None env_empty de

let val_decl ~keep_loc _ = ignore(keep_loc); assert false (* keep_loc:bool -> dval_decl -> let_sym *)
let let_defn ~keep_loc _ = ignore(keep_loc); assert false (* keep_loc:bool -> dlet_defn -> let_defn *)
let fun_defn ~keep_loc _ = ignore(keep_loc); assert false (* keep_loc:bool -> dfun_defn -> fun_defn *)
let rec_defn ~keep_loc _ = ignore(keep_loc); assert false (* keep_loc:bool -> dfun_defn list -> fun_defn list *)
