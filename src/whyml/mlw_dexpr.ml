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

open Wstdlib
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
let dity_bool = Dpur (ts_bool, [])
let dity_unit = Dpur (ts_unit, [])

let dvty_bool = [], dity_bool
let dvty_unit = [], dity_unit

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
  let rec print_dity pri fmt = function
    | Dvar { contents = Dtvs tv }
    | Dutv tv -> Pretty.print_tv fmt tv
    | Dvar { contents = Dval dty } -> print_dity pri fmt dty
    | Dpur (s,[t1;t2]) when ts_equal s Ty.ts_func ->
        Format.fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
          (print_dity 1) t1 (print_dity 0) t2
    | Dpur (s,tl) when is_ts_tuple s -> Format.fprintf fmt "(%a)"
        (Pp.print_list Pp.comma (print_dity 0)) tl
    | Dpur (s,[]) -> Pretty.print_ts fmt s
    | Dpur (s,tl) -> Format.fprintf fmt (protect_on (pri > 1) "%a@ %a")
        Pretty.print_ts s (Pp.print_list Pp.space (print_dity 2)) tl
    | Dapp (s,[],rl) -> Format.fprintf fmt (protect_on (pri > 1) "%a@ <%a>")
        Mlw_pretty.print_its s (Pp.print_list Pp.comma print_dreg) rl
    | Dapp (s,tl,rl) -> Format.fprintf fmt (protect_on (pri > 1) "%a@ <%a>@ %a")
        Mlw_pretty.print_its s (Pp.print_list Pp.comma print_dreg) rl
          (Pp.print_list Pp.space (print_dity 2)) tl
  and print_dreg fmt = function
    | Rreg (r,_) when Debug.test_flag debug_print_reg_types ->
        Format.fprintf fmt "@[%a:@,%a@]" Mlw_pretty.print_reg r
          Mlw_pretty.print_ity r.reg_ity
    | Rreg (r,_) -> Mlw_pretty.print_reg fmt r
    | Rvar { contents = Rtvs (tv,dity) }
      when Debug.test_flag debug_print_reg_types ->
        Format.fprintf fmt "@[%a:@,%a@]" print_rtvs tv (print_dity 0) dity
    | Rvar { contents = Rtvs (tv,_) } -> print_rtvs fmt tv
    | Rvar { contents = Rval dreg } -> print_dreg fmt dreg
  in
  print_dity 0 fmt dity

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
    if not (Stv.mem tv tvs) then dity_unify_weak v dity;
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
  | DPcast of dpattern * ity

(** Specifications *)

type ghost = bool

type opaque = Stv.t

type dbinder = preid option * ghost * opaque * dity

type 'a later = vsymbol Mstr.t -> 'a
  (* specification terms are parsed and typechecked after the program
     expressions, when the types of locally bound program variables are
     already established. *)

type dspec_final = {
  ds_pre     : term list;
  ds_post    : (vsymbol option * term) list;
  ds_xpost   : (vsymbol option * term) list Mexn.t;
  ds_reads   : vsymbol list;
  ds_writes  : term list;
  ds_variant : variant list;
  ds_checkrw : bool;
  ds_diverge : bool;
}

type dspec = ty -> dspec_final
  (* Computation specification is also parametrized by the result type.
     All vsymbols in the postcondition clauses in the [ds_post] field
     must have this type. All vsymbols in the exceptional postcondition
     clauses must have the type of the corresponding exception. *)

type dtype_v =
  | DSpecV of dity
  | DSpecA of dbinder list * dtype_c

and dtype_c = dtype_v * dspec later

(** Expressions *)

type dinvariant = term list

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
  | DEapply of dexpr * dexpr
  | DEconst of Number.constant * ity
  | DElam of dbinder list * dexpr * dspec later
  | DElet of dlet_defn * dexpr
  | DEfun of dfun_defn * dexpr
  | DErec of drec_defn * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEcase of dexpr * (dpattern * dexpr) list
  | DEassign of plsymbol * dexpr * dexpr
  | DElazy of dlazy_op * dexpr * dexpr
  | DEnot of dexpr
  | DEtrue
  | DEfalse
  | DEraise of xsymbol * dexpr
  | DEtry of dexpr * (xsymbol * dpattern * dexpr) list
  | DEfor of preid * dexpr * for_direction * dexpr * dinvariant later * dexpr
  | DEwhile of dexpr * (variant list * dinvariant) later * dexpr
  | DEloop of (variant list * dinvariant) later * dexpr
  | DEabsurd
  | DEassert of assertion_kind * term later
  | DEabstract of dexpr * dspec later
  | DEmark of preid * dexpr
  | DEghost of dexpr
  | DEany of dtype_v * dspec later option
  | DEcast of dexpr * ity
  | DEuloc of dexpr * Loc.position
  | DElabel of dexpr * Slab.t

and dlet_defn = preid * ghost * dexpr

and dfun_defn = preid * ghost * dbinder list * dexpr * dspec later

and drec_defn = { fds : dfun_defn list }

type dval_decl = preid * ghost * dtype_v

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

let denv_add_var denv id dity = denv_add_mono denv id ([], dity)

let denv_add_let denv (id,_,({de_dvty = dvty} as de)) =
  if fst dvty = [] then denv_add_mono denv id dvty else
  let rec is_value de = match de.de_node with
    | DEghost de | DEuloc (de,_) | DElabel (de,_) -> is_value de
    | DEvar _ | DEgpsym _ | DElam _ | DEany (_,None) -> true
    | _ -> false in
  if is_value de
  then denv_add_poly denv id dvty
  else denv_add_mono denv id dvty

let denv_add_fun denv (id,_,bl,{de_dvty = (argl,res)},_) =
  if bl = [] then invalid_arg "Mlw_dexpr.denv_add_fun: empty argument list";
  let argl = List.fold_right (fun (_,_,_,t) l -> t::l) bl argl in
  denv_add_poly denv id (argl, res)

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

let dity_unify_app ls fn (l1: 'a list) (l2: dity list) =
  try List.iter2 fn l1 l2 with Invalid_argument _ ->
    raise (BadArity (ls, List.length l1))

let dpat_expected_type {dp_dity = dp_dity; dp_loc = loc} dity =
  try dity_unify dp_dity dity with Exit -> Loc.errorm ?loc
    "This pattern has type %a,@ but is expected to have type %a"
    print_dity dp_dity print_dity dity

let dpat_expected_type_weak {dp_dity = dp_dity; dp_loc = loc} dity =
  try dity_unify_weak dp_dity dity with Exit -> Loc.errorm ?loc
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

(** Generation of letrec blocks *)

type pre_fun_defn =
  preid * ghost * dbinder list * dity * (denv -> dexpr * dspec later)

exception DupId of preid

let drec_defn denv0 prel =
  if prel = [] then invalid_arg "Mlw_dexpr.drec_defn: empty function list";
  let add s (id,_,_,_,_) = Sstr.add_new (DupId id) id.pre_name s in
  let _ = try List.fold_left add Sstr.empty prel with DupId id ->
    Loc.errorm ?loc:id.pre_loc "duplicate function name %s" id.pre_name in
  let add denv (id,_,bl,res,_) =
    if bl = [] then invalid_arg "Mlw_dexpr.drec_defn: empty argument list";
    let argl = List.map (fun (_,_,_,t) -> t) bl in
    denv_add_rec denv denv0.frozen id (argl,res) in
  let denv1 = List.fold_left add denv0 prel in
  let parse (id,gh,bl,res,pre) =
    let de, dsp = pre (denv_add_args denv1 bl) in
    dexpr_expected_type_weak de res;
    (id,gh,bl,de,dsp) in
  let fdl = List.map parse prel in
  let add denv ((id,_,_,_,_) as fd) =
    let check tv = if is_frozen denv0.frozen tv then Loc.errorm ?loc:id.pre_loc
      "This function is expected to be polymorphic in type variable %a"
      Pretty.print_tv tv in
    begin match Mstr.find_opt id.pre_name denv1.locals with
    | Some (Some tvs, _) -> Stv.iter check tvs
    | Some (None, _) | None -> assert false
    end;
    denv_add_fun denv fd in
  List.fold_left add denv0 fdl, { fds = fdl }

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
    | DPcast (dp, ity) ->
        dpat_expected_type_weak dp (dity_of_ity ity);
        dp
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
    | DEapply ({de_dvty = (dity::argl, res)}, de2) ->
        dexpr_expected_type de2 dity;
        argl, res
    | DEapply ({de_dvty = ([],res)} as de1, de2) ->
        let rec not_arrow = function
          | Dvar {contents = Dval dity} -> not_arrow dity
          | Dpur (ts,_) -> not (ts_equal ts Ty.ts_func)
          | Dvar _ -> false | _ -> true in
        if not_arrow res then Loc.errorm ?loc:de1.de_loc
          "This expression has type %a,@ it cannot be applied" print_dity res;
        let argl, res = specialize_ls fs_func_app in
        dity_unify_app fs_func_app dexpr_expected_type [de1;de2] argl;
        [], res
    | DEconst (_, ity) -> [], dity_of_ity ity
    | DEfun ((_,_,[],_,_),_) ->
        invalid_arg "Mlw_dexpr.dexpr: empty argument list in DEfun"
    | DElet (_,de)
    | DEfun (_,de)
    | DErec (_,de) ->
        de.de_dvty
    | DElam ([],_,_) ->
        invalid_arg "Mlw_dexpr.dexpr: empty argument list in DElam"
    | DElam (bl,{de_dvty = (argl,res)},_) ->
        List.fold_right (fun (_,_,_,t) l -> t::l) bl argl, res
    | DEif (de1,de2,de3) ->
        let res = dity_fresh () in
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 res;
        dexpr_expected_type de3 res;
        de2.de_dvty
    | DEcase (_,[]) ->
        invalid_arg "Mlw_dexpr.dexpr: empty branch list in DEcase"
    | DEcase (de,bl) ->
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
        dvty_unit
    | DElazy (_,de1,de2) ->
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 dity_bool;
        de1.de_dvty
    | DEnot de ->
        dexpr_expected_type de dity_bool;
        de.de_dvty
    | DEtrue
    | DEfalse ->
        dvty_bool
    | DEraise (xs,de) ->
        dexpr_expected_type de (specialize_xs xs);
        [], dity_fresh ()
    | DEtry (_,[]) ->
        invalid_arg "Mlw_dexpr.dexpr: empty branch list in DEtry"
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
    | DEwhile (de1,_,de2) ->
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 dity_unit;
        de2.de_dvty
    | DEloop (_,de) ->
        dexpr_expected_type de dity_unit;
        de.de_dvty
    | DEabsurd ->
        [], dity_fresh ()
    | DEassert _ ->
        dvty_unit
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

let mk_dexpr loc d n = { de_node = n; de_dvty = d; de_loc = loc }

let de_void loc = mk_dexpr loc dvty_unit (DElsapp (fs_void, []))

let pat_void loc = { dp_pat = PPlapp (fs_void, []);
  dp_dity = dity_unit; dp_vars = Mstr.empty; dp_loc = loc }

(** Final stage *)

(** Binders *)

let binders bl =
  let sn = ref Sstr.empty in
  let binder (id, ghost, _, dity) =
    let id = match id with
      | Some ({pre_name = n} as id) ->
          let exn = match id.pre_loc with
            | Some loc -> Loc.Located (loc, Dterm.DuplicateVar n)
            | None -> Dterm.DuplicateVar n in
          sn := Sstr.add_new exn n !sn; id
      | None -> id_fresh "_" in
    create_pvsymbol id ~ghost (ity_of_dity dity) in
  List.map binder bl

let opaque_binders otv bl =
  List.fold_left (fun otv (_,_,s,_) -> Stv.union otv s) otv bl

(** Specifications *)

let to_fmla f = match f.t_ty with
  | None -> f
  | Some ty when ty_equal ty ty_bool -> t_equ f t_bool_true
  | _ -> Loc.error ?loc:f.t_loc Dterm.FmlaExpected

let create_assert f = t_label_add Split_goal.stop_split (to_fmla f)
let create_pre fl = t_and_simp_l (List.map create_assert fl)
let create_inv = create_pre

let create_post u (v,f) =
  let f = match v with
    | Some v when vs_equal u v -> f
    | Some v -> Loc.try3 ?loc:f.t_loc t_subst_single v (t_var u) f
    | None -> f in
  let f = Mlw_wp.remove_old (to_fmla f) in
  t_label_add Split_goal.stop_split f

let create_post ty ql =
  let rec get_var = function
    | [] -> create_vsymbol (id_fresh "result") ty
    | (Some v, _) :: _ -> Ty.ty_equal_check ty v.vs_ty; v
    | _ :: l -> get_var l in
  let u = get_var ql in
  let f = t_and_simp_l (List.map (create_post u) ql) in
  Mlw_ty.create_post u f

let create_xpost xql =
  Mexn.mapi (fun xs ql -> create_post (ty_of_ity xs.xs_ity) ql) xql

let spec_of_dspec eff ty dsp = {
  c_pre     = create_pre dsp.ds_pre;
  c_post    = create_post ty dsp.ds_post;
  c_xpost   = create_xpost dsp.ds_xpost;
  c_effect  = eff;
  c_variant = dsp.ds_variant;
  c_letrec  = 0;
}

(** User effects *)

let mk_field ity gh mut = {fd_ity = ity; fd_ghost = gh; fd_mut = mut}

let rec effect_of_term t = match t.t_node with
  | Tvar vs ->
      let pv = try restore_pv vs with Not_found ->
        Loc.errorm ?loc:t.t_loc "unsupported effect expression" in
      vs, mk_field pv.pv_ity pv.pv_ghost None
  | Tapp (fs,[ta]) ->
      let vs, fa = effect_of_term ta in
      let ofa,ofv = try match restore_pl fs with
        | {pl_args = [ofa]; pl_value = ofv} ->
            ofa, ofv
        | _ -> assert false
      with Not_found -> match fs with
        | {ls_args = [tya]; ls_value = Some tyv} ->
            mk_field (ity_of_ty tya) false None,
            mk_field (ity_of_ty tyv) false None
        | {ls_args = [_]; ls_value = None} ->
            Loc.errorm ?loc:t.t_loc "unsupported effect expression"
        | _ -> assert false in
      let sbs = ity_match ity_subst_empty ofa.fd_ity fa.fd_ity in
      let ity = try ity_full_inst sbs ofv.fd_ity with Not_found ->
        Loc.errorm ?loc:t.t_loc "unsupported effect expression" in
      let gh = (fa.fd_ghost && not ofa.fd_ghost) || ofv.fd_ghost in
      let mut = Opt.map (reg_full_inst sbs) ofv.fd_mut in
      vs, mk_field ity gh mut
  | _ ->
      Loc.errorm ?loc:t.t_loc "unsupported effect expression"

let effect_of_dspec dsp =
  let add_raise xs _ eff = eff_raise eff xs in
  let eff = Mexn.fold add_raise dsp.ds_xpost eff_empty in
  let eff = if dsp.ds_diverge then eff_diverge eff else eff in
  let svs = List.fold_right Svs.add dsp.ds_reads Svs.empty in
  let add_write (svs,mreg,eff) t =
    let vs, fd = effect_of_term t in
    match fd.fd_mut, fd.fd_ity.ity_node with
    | Some reg, _ ->
        Svs.add vs svs, Mreg.add reg t mreg,
        eff_write eff ~ghost:fd.fd_ghost reg
    | None, Ityapp ({its_ghrl = ghrl},_,(_::_ as regl)) ->
        let add_reg mreg reg = Mreg.add reg t mreg in
        let add_write eff gh reg =
          eff_write eff ~ghost:(fd.fd_ghost || gh) reg in
        Svs.add vs svs, List.fold_left add_reg mreg regl,
        List.fold_left2 add_write eff ghrl regl
    | _ ->
        Loc.errorm ?loc:t.t_loc "mutable expression expected"
  in
  List.fold_left add_write (svs,Mreg.empty,eff) dsp.ds_writes

let e_find_loc pr e =
  try (e_find (fun e -> e.e_loc <> None && pr e) e).e_loc
  with Not_found -> None

let lab_w_diverges_no = Ident.create_label "W:diverges:N"

let check_user_effect ?ps e spec args dsp =
  let has_write reg eff =
    Sreg.mem reg eff.eff_writes || Sreg.mem reg eff.eff_ghostw in
  let has_raise xs eff =
    Sexn.mem xs eff.eff_raises || Sexn.mem xs eff.eff_ghostx in
  (* computed effect vs user effect *)
  let eeff = spec.c_effect in
  let args = Spv.of_list args in
  let full_xpost = ps <> None in
  let usvs, mreg, ueff = effect_of_dspec dsp in
  (* check that every user effect actually happens *)
  let check_read vs =
    let pv = try restore_pv vs with Not_found ->
      Loc.errorm "unsupported@ effect@ expression" in
    if Spv.mem pv args then Warning.emit ?loc:e.e_loc
      "variable@ %a@ is@ a@ local@ function@ argument,@ \
        it@ does@ not@ have@ to@ be@ listed@ in@ the@ `reads'@ clause"
      Pretty.print_vs vs;
    if not (Spv.mem pv e.e_syms.syms_pv) then Loc.errorm ?loc:e.e_loc
      "variable@ %a@ does@ not@ occur@ in@ this@ expression"
      Pretty.print_vs vs in
  List.iter check_read dsp.ds_reads;
  let check_write reg = if not (has_write reg eeff)
    then let t = Mreg.find reg mreg in Loc.errorm ?loc:t.t_loc
      "this@ write@ effect@ does@ not@ happen@ in@ the@ expression" in
  Sreg.iter check_write ueff.eff_writes;
  Sreg.iter check_write ueff.eff_ghostw;
  let check_raise xs _ = if not (has_raise xs eeff)
    then Loc.errorm ?loc:e.e_loc
      "this@ expression@ does@ not@ raise@ exception@ %a"
      Mlw_pretty.print_xs xs in
  Mexn.iter check_raise ueff.eff_raises;
  Mexn.iter check_raise ueff.eff_ghostx;
  if ueff.eff_diverg && not eeff.eff_diverg then
    Loc.errorm ?loc:e.e_loc "this@ expression@ does@ not@ diverge";
  (* check that every computed effect is listed *)
  let check_read pv = if not (Svs.mem pv.pv_vs usvs) then
    Loc.errorm ?loc:(e_find_loc (fun e -> Spv.mem pv e.e_syms.syms_pv) e)
      "this@ expression@ depends@ on@ variable@ %a@ \
        left@ out@ in@ the@ specification" Mlw_pretty.print_pv pv in
  let check_write reg = if not (has_write reg ueff) then
    Loc.errorm ?loc:(e_find_loc (fun e -> has_write reg e.e_effect) e)
      "this@ expression@ produces@ an@ unlisted@ write@ effect" in
  if dsp.ds_checkrw then begin
    let reads = Spv.remove Mlw_decl.pv_old e.e_syms.syms_pv in
    let reads = Spv.diff reads (spec_pvset Spv.empty spec) in
    Spv.iter check_read (Spv.diff reads args);
    Sreg.iter check_write eeff.eff_writes;
    Sreg.iter check_write eeff.eff_ghostw;
  end;
  let check_raise xs = if not (has_raise xs ueff) then
    Loc.errorm ?loc:(e_find_loc (fun e -> has_raise xs e.e_effect) e)
      "this@ expression@ raises@ unlisted@ exception@ %a"
      Mlw_pretty.print_xs xs in
  if full_xpost then Sexn.iter check_raise eeff.eff_raises;
  if full_xpost then Sexn.iter check_raise eeff.eff_ghostx;
  if eeff.eff_diverg && not ueff.eff_diverg then match ps with
    | Some {ps_name = {id_label = l}}
      when not (Slab.mem lab_w_diverges_no l) ->
        Warning.emit ?loc:(e_find_loc (fun e -> e.e_effect.eff_diverg) e)
          "this@ expression@ may@ diverge,@ \
            which@ is@ not@ stated@ in@ the@ specification"
    | _ -> ()

let check_lambda_effect ({fun_lambda = lam} as fd) bl dsp =
  let spec = fd.fun_ps.ps_aty.aty_spec in
  let args = fd.fun_ps.ps_aty.aty_args in
  check_user_effect ~ps:fd.fun_ps lam.l_expr spec args dsp;
  let optv = opaque_binders Stv.empty bl in
  let bad_comp tv _ _ = Loc.errorm
    ?loc:(e_find_loc (fun e -> Stv.mem tv e.e_effect.eff_compar) lam.l_expr)
    "type parameter %a is not opaque in this expression" Pretty.print_tv tv in
  ignore (Mtv.inter bad_comp optv spec.c_effect.eff_compar)

let check_user_ps recu ps =
  let ps_regs = ps.ps_subst.ity_subst_reg in
  let report r =
    if Mreg.mem r ps_regs then let spv = Spv.filter
        (fun pv -> reg_occurs r pv.pv_ity.ity_vars) ps.ps_pvset in
      Loc.errorm "The type of this function contains an alias with \
        external variable %a" Mlw_pretty.print_pv (Spv.choose spv)
    else
      Loc.errorm "The type of this function contains an alias"
  in
  let rec check regs ity = match ity.ity_node with
    | Ityapp (_,_,rl) ->
        let add regs r =
          if Mreg.mem r regs then report r else
          check (Mreg.add r r regs) r.reg_ity in
        let regs = List.fold_left add regs rl in
        ity_fold check regs ity
    | _ ->
        ity_fold check regs ity
  in
  let rec down regs a =
    let add regs pv = check regs pv.pv_ity in
    let regs = List.fold_left add regs a.aty_args in
    match a.aty_result with
    | VTarrow a -> down regs a
    | VTvalue v -> check (if recu then regs else ps_regs) v
    (* we allow the value in a non-recursive function to contain
       regions coming the function's arguments, but not from the
       context. It is sometimes useful to write a function around
       a constructor or a projection. For recursive functions, we
       impose the full non-alias discipline, to ensure the safety
       of region polymorphism (see add_rec_mono). *)
  in
  ignore (down ps_regs ps.ps_aty)

(** Environment *)

type local_env = {
   kn : Mlw_decl.known_map;
  lkn : Decl.known_map;
  psm : psymbol Mstr.t;
  pvm : pvsymbol Mstr.t;
  vsm : vsymbol Mstr.t;
}

let env_empty lkn kn = {
   kn = kn;
  lkn = lkn;
  psm = Mstr.empty;
  pvm = Mstr.empty;
  vsm = Mstr.empty;
}

let add_psymbol ({psm = psm} as lenv) ps =
  let n = ps.ps_name.id_string in
  { lenv with psm = Mstr.add n ps psm }

let add_pvsymbol ({pvm = pvm; vsm = vsm} as lenv) pv =
  let n = pv.pv_vs.vs_name.id_string in
  { lenv with pvm = Mstr.add n pv pvm; vsm = Mstr.add n pv.pv_vs vsm }

let add_pv_map ({pvm = pvm; vsm = vsm} as lenv) vm =
  let um = Mstr.map (fun pv -> pv.pv_vs) vm in
  { lenv with pvm = Mstr.set_union vm pvm; vsm = Mstr.set_union um vsm }

let add_let_sym env = function
  | LetV pv -> add_pvsymbol env pv
  | LetA ps -> add_psymbol env ps

let add_fundef  env fd  = add_psymbol env fd.fun_ps
let add_fundefs env fdl = List.fold_left add_fundef env fdl
let add_binders env pvl = List.fold_left add_pvsymbol env pvl

(** Invariant handling *)

let env_invariant {lkn = lkn; kn = kn} eff pvs =
  let regs = Sreg.union eff.eff_writes eff.eff_ghostw in
  let add_pv pv (pinv,qinv) =
    let ity = pv.pv_ity in
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
      Loc.errorm "Variable %s is reset and can only be used \
        under `old' in the postcondition" vs.vs_name.id_string
  | Tapp (ls,_) when ls_equal ls Mlw_wp.fs_at -> false
  | Tlet _ | Tcase _ | Teps _ | Tquant _ ->
      let rvs = Mvs.set_inter rvs (t_vars t) in
      if Mvs.is_empty rvs then false else
      t_any (check_reset rvs) t
  | _ ->
      t_any (check_reset rvs) t

let post_invariant {lkn = lkn; kn = kn} rvs inv ity q =
  ignore (check_reset rvs q);
  let vs, q = open_post q in
  let res_inv = Mlw_wp.full_invariant lkn kn vs ity in
  let q = t_and_asym_simp (t_and_simp res_inv inv) q in
  Mlw_ty.create_post vs q

let reset_vars eff pvs =
  let add pv s =
    if eff_stale_region eff pv.pv_ity.ity_vars
    then Svs.add pv.pv_vs s else s in
  if Mreg.is_empty eff.eff_resets then Svs.empty else
  Spv.fold add pvs Svs.empty

let spec_invariant env pvs vty spec =
  let ity = ity_of_vty vty in
  let pvs = spec_pvset pvs spec in
  let rvs = reset_vars spec.c_effect pvs in
  let pinv,qinv = env_invariant env spec.c_effect pvs in
  let post_inv = post_invariant env rvs qinv in
  let xpost_inv xs q = post_inv xs.xs_ity q in
  { spec with c_pre   = t_and_asym_simp pinv spec.c_pre;
              c_post  = post_inv ity spec.c_post;
              c_xpost = Mexn.mapi xpost_inv spec.c_xpost }

(** Abstract values *)

let warn_unused s loc =
  if not (Debug.test_flag Dterm.debug_ignore_unused_var) then
  if s = "" || s.[0] <> '_' then
  Warning.emit ?loc "unused variable %s" s

let check_used_pv e pv = if not (Spv.mem pv e.e_syms.syms_pv) then
  warn_unused pv.pv_vs.vs_name.id_string pv.pv_vs.vs_name.id_loc

let check_used_ps e ps = if not (Sps.mem ps e.e_syms.syms_ps) then
  warn_unused ps.ps_name.id_string ps.ps_name.id_loc

let rec type_c env pvs vars otv (dtyv, dsp) =
  let vty = type_v env pvs vars otv dtyv in
  let res = ty_of_vty vty in
  let dsp = dsp env.vsm res in
  let esvs, _, eff = effect_of_dspec dsp in
  (* refresh every subregion of a modified region *)
  let writes = Sreg.union eff.eff_writes eff.eff_ghostw in
  let check u eff =
    reg_fold (fun r e -> eff_refresh e r u) u.reg_ity.ity_vars eff in
  let eff = Sreg.fold check writes eff in
  (* eff_compare every type variable not marked as opaque *)
  let eff = Stv.fold_left eff_compare eff (Stv.diff vars.vars_tv otv) in
  (* make spec *)
  let spec = spec_of_dspec eff res dsp in
  if spec.c_variant <> [] then Loc.errorm
    "variants are not allowed in a parameter declaration";
  (* we add a fake variant term for every external variable in effect
     expressions which also does not occur in pre/post/xpost. In this
     way, we store the variable in the specification in order to keep
     the effect from being erased by Mlw_ty.spec_filter. Variants are
     ignored outside of "let rec" definitions, so WP are not affected. *)
  let del_pv pv s = Svs.remove pv.pv_vs s in
  let esvs = Spv.fold del_pv pvs esvs in
  let drop _ t s = Mvs.set_diff s (t_vars t) in
  let esvs = drop () spec.c_pre esvs in
  let esvs = drop () spec.c_post esvs in
  let esvs = Mexn.fold drop spec.c_xpost esvs in
  let add_vs vs varl = (t_var vs, None) :: varl in
  let varl = Svs.fold add_vs esvs spec.c_variant in
  let spec = { spec with c_variant = varl } in
  spec, vty

and type_v env pvs vars otv = function
  | DSpecV v ->
      VTvalue (ity_of_dity v)
  | DSpecA (bl,tyc) ->
      let pvl = binders bl in
      let env = add_binders env pvl in
      let otv = opaque_binders otv bl in
      let add_pv pv s = vars_union pv.pv_ity.ity_vars s in
      let vars = List.fold_right add_pv pvl vars in
      let pvs = List.fold_right Spv.add pvl pvs in
      let spec, vty = type_c env pvs vars otv tyc in
      let spec = spec_invariant env pvs vty spec in
      VTarrow (vty_arrow pvl ~spec vty)

let val_decl env (id,ghost,dtyv) =
  match type_v env Spv.empty vars_empty Stv.empty dtyv with
  | VTvalue v -> LetV (create_pvsymbol id ~ghost v)
  | VTarrow a -> LetA (create_psymbol id ~ghost a)

(** Expressions *)

let implicit_post = Debug.register_flag "implicit_post"
  ~desc:"Generate@ a@ postcondition@ for@ pure@ functions@ without@ one."

let e_ghostify gh e =
  if gh && not e.e_ghost then e_ghost e else e

let rec strip uloc labs de = match de.de_node with
  | DEcast (de,_) -> strip uloc labs de
  | DEuloc (de,loc) -> strip (Some loc) labs de
  | DElabel (de,s) -> strip uloc (Slab.union labs s) de
  | _ -> uloc, labs, de

let rec expr ~keep_loc uloc env ({de_loc = loc} as de) =
  let uloc, labs, de = strip uloc Slab.empty de in
  let e = Loc.try4 ?loc try_expr keep_loc uloc env de in
  let loc = if keep_loc then loc else None in
  let loc = if uloc <> None then uloc else loc in
  if loc = None && Slab.is_empty labs then e else
  e_label ?loc labs e

and try_expr keep_loc uloc env ({de_dvty = argl,res} as de0) =
  let get env de = expr ~keep_loc uloc env de in
  match de0.de_node with
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
      let get_gh fd de = e_ghostify fd.fd_ghost (get env de) in
      e_plapp pl (List.map2 get_gh pl.pl_args del) (ity_of_dity res)
  | DElsapp (ls,del) ->
      e_lapp ls (List.map (get env) del) (ity_of_dity res)
  | DEapply ({de_dvty = (_::_, _)} as de1,de2) ->
      let e1 = get env de1 in
      let gh = match e1.e_vty with
        | VTarrow {aty_args = pv::_} -> pv.pv_ghost
        | _ -> assert false in
      e_app e1 [e_ghostify gh (get env de2)]
  | DEapply (de1,de2) ->
      e_lapp fs_func_app [get env de1; get env de2] (ity_of_dity res)
  | DEconst (c,ity) ->
      e_const c ity
  | DElet ((id,gh,de1),de2) ->
      let e1 = get env de1 in
      let mk_expr e1 =
        let e1 = e_ghostify gh e1 in
        let ld1 = create_let_defn id e1 in
        let env = add_let_sym env ld1.let_sym in
        let e2 = get env de2 in
        let e2_unit = match e2.e_vty with
          | VTvalue ity -> ity_equal ity ity_unit
          | _ -> false in
        let id_in_e2 = match ld1.let_sym with
          | LetV pv -> Spv.mem pv e2.e_syms.syms_pv
          | LetA ps -> Sps.mem ps e2.e_syms.syms_ps in
        (* ??? N214-006 disable this warning globally until better option is
           available
        if not id_in_e2 then warn_unused id.pre_name id.pre_loc;
        *)
        let e1_no_eff =
          Sreg.is_empty e1.e_effect.eff_writes &&
          Sexn.is_empty e1.e_effect.eff_raises &&
          not e1.e_effect.eff_diverg &&
          (* if e1 is a recursive call, we may not know yet its effects,
             so we have to rely on an heuristic: if the result of e1 is
             not used in e2, then it was probably called for the effect. *)
          id_in_e2
        in
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
        | VTarrow _ when e1.e_ghost && not gh -> (* TODO: localize *)
            Loc.errorm "%s must be a ghost function" id.pre_name
        | VTarrow _ -> flatten e1
        | VTvalue _ -> mk_expr e1
      end
  | DEif (de1,de2,de3) ->
      let e1 = get env de1 in
      let e2 = get env de2 in
      let e3 = get env de3 in
      e_if e1 e2 e3
  | DEcase (de1,bl) ->
      let e1 = get env de1 in
      let ity = ity_of_expr e1 in
      let ghost = e1.e_ghost in
      let branch (dp,de) =
        let vm, pat = make_ppattern dp.dp_pat ~ghost ity in
        let e = get (add_pv_map env vm) de in
        Mstr.iter (fun _ pv -> check_used_pv e pv) vm;
        pat, e in
      e_case e1 (List.map branch bl)
  | DEassign (pl,de1,de2) ->
      e_assign pl (get env de1) (get env de2)
  | DElazy (DEand,de1,de2) ->
      e_lazy_and (get env de1) (get env de2)
  | DElazy (DEor,de1,de2) ->
      e_lazy_or (get env de1) (get env de2)
  | DEnot de ->
      e_not (get env de)
  | DEtrue ->
      e_true
  | DEfalse ->
      e_false
  | DEraise (xs,de) ->
      e_raise xs (get env de) (ity_of_dity res)
  | DEtry (de1,bl) ->
      let e1 = get env de1 in
      let add_branch (m,l) (xs,dp,de) =
        let vm, pat = make_ppattern dp.dp_pat xs.xs_ity in
        let e = get (add_pv_map env vm) de in
        Mstr.iter (fun _ pv -> check_used_pv e pv) vm;
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
            let pl = List.rev_map (fun (p,_) -> [p.ppat_pattern]) bl in
            let bl = if Pattern.is_exhaustive [t_var pv.pv_vs] pl
              then bl else let _,pp = make_ppattern PPwild pv.pv_ity in
              (pp, e_raise xs (e_value pv) (ity_of_dity res)) :: bl in
            xs, pv, e_case (e_value pv) (List.rev bl)
      in
      e_try e1 (List.rev_map mk_branch xsl)
  | DEfor (id,de_from,dir,de_to,dinv,de) ->
      let e_from = get env de_from in
      let e_to = get env de_to in
      let pv = create_pvsymbol id ity_int in
      let env = add_pvsymbol env pv in
      let e = get env de in
      let inv = dinv env.vsm in
      e_for pv e_from dir e_to (create_inv inv) e
  | DEwhile (de1,varl_inv,de2) ->
      let loc = de0.de_loc in
      let de3 = mk_dexpr loc dvty_unit
        (DEtry (mk_dexpr loc dvty_unit
          (DEloop (varl_inv, mk_dexpr loc dvty_unit
            (DEif (de1, de2, mk_dexpr loc dvty_unit
              (DEraise (Mlw_module.xs_exit, de_void loc)))))),
          [Mlw_module.xs_exit, pat_void loc, de_void loc])) in
      try_expr keep_loc uloc env de3
  | DEloop (varl_inv,de) ->
      let e = get env de in
      let varl, inv = varl_inv env.vsm in
      e_loop (create_inv inv) varl e
  | DEabsurd ->
      e_absurd (ity_of_dity res)
  | DEassert (ak,f) ->
      e_assert ak (create_assert (f env.vsm))
  | DEabstract (de,dsp) ->
      let e = get env de in
      let tyv = ty_of_vty e.e_vty in
      let dsp = dsp env.vsm tyv in
      if dsp.ds_variant <> [] then Loc.errorm
        "variants are not allowed in `abstract'";
      let spec = spec_of_dspec e.e_effect tyv dsp in
      check_user_effect e spec [] dsp;
      let speci = spec_invariant env e.e_syms.syms_pv e.e_vty spec in
      (* we do not require invariants on free variables *)
      let spec = { speci with c_pre = spec.c_pre } in
      (* no user post => we try to purify *)
      let spec = if dsp.ds_post <> [] then spec else match e_purify e with
        | Some t ->
          let vs, f = Mlw_ty.open_post spec.c_post in
          let f = t_and_simp (t_equ_simp (t_var vs) t) f in
          let f = t_label_add Split_goal.stop_split f in
          let post = Mlw_ty.create_post vs f in
          { spec with c_post = post }
        | None -> spec in
      e_abstract e spec
  | DEmark (id,de) ->
      let ld = create_let_defn id Mlw_wp.e_now in
      let env = add_let_sym env ld.let_sym in
      e_let ld (get env de)
  | DEghost de -> (* keep user ghost annotations even if redundant *)
      e_ghost (get env de)
  | DEany (dtyv, Some dsp) -> (* we do not add invariants to the top spec *)
      let spec, vty = type_c env Spv.empty vars_empty Stv.empty (dtyv,dsp) in
      e_any (Some spec) vty
  | DEany (dtyv, None) ->
      e_any None (type_v env Spv.empty vars_empty Stv.empty dtyv)
  | DEfun (fd,de) ->
      let fd = expr_fun ~keep_loc ~strict:true uloc env fd in
      let e = get (add_fundef env fd) de in
      check_used_ps e fd.fun_ps;
      e_rec [fd] e
  | DElam (bl,de,sp) ->
      let fd = id_fresh "fn", false, bl, de, sp in
      let fd = expr_fun ~keep_loc ~strict:false uloc env fd in
      let de = { de0 with de_node = DEgpsym fd.fun_ps } in
      e_rec [fd] (get env de)
  | DErec (fdl,de) ->
      let fdl = expr_rec ~keep_loc uloc env fdl in
      let e = get (add_fundefs env fdl) de in
      e_rec fdl e
  | DEcast _ | DEuloc _ | DElabel _ ->
      assert false (* already stripped *)

and expr_rec ~keep_loc uloc env {fds = dfdl} =
  let step1 env (id, gh, bl, de, dsp) =
    let pvl = binders bl in
    if fst de.de_dvty <> [] then Loc.errorm ?loc:de.de_loc
      "The body of a recursive function must be a first-order value";
    let aty = vty_arrow pvl (VTvalue (ity_of_dity (snd de.de_dvty))) in
    let ps = create_psymbol id ~ghost:gh aty in
    add_psymbol env ps, (ps, gh, bl, pvl, de, dsp) in
  let env, fdl = Lists.map_fold_left step1 env dfdl in
  let step2 (ps, gh, bl, pvl, de, dsp) (fdl, dfdl) =
    let lam, dsp =
      expr_lam ~keep_loc ~strict:true uloc env gh pvl de dsp in
    (ps, lam) :: fdl, (ps.ps_name, gh, bl, de, dsp) :: dfdl in
  (* check for unexpected aliases in case of trouble *)
  let fdl, dfdl = try List.fold_right step2 fdl ([],[]) with
    | Loc.Located (_, Mlw_ty.TypeMismatch _)
    | Mlw_ty.TypeMismatch _ as exn ->
        List.iter (fun (ps,_,_,_,_,_) ->
          let loc = Opt.get ps.ps_name.Ident.id_loc in
          Loc.try2 ~loc check_user_ps true ps) fdl;
        raise exn in
  let fdl = try create_rec_defn fdl with
    | Loc.Located (_, Mlw_ty.TypeMismatch _)
    | Mlw_ty.TypeMismatch _ as exn ->
        List.iter (fun (ps,lam) ->
          let loc = Opt.get ps.ps_name.Ident.id_loc in
          let fd = create_fun_defn (id_clone ps.ps_name) lam in
          Loc.try2 ~loc check_user_ps true fd.fun_ps) fdl;
        raise exn in
  let step3 { fun_ps = ps; fun_lambda = lam } =
    let { l_spec = spec; l_expr = e } = lam in
    let spec = spec_invariant env e.e_syms.syms_pv e.e_vty spec in
    ps, { lam with l_spec = { spec with c_letrec = 0 }} in
  let fdl = create_rec_defn (List.map step3 fdl) in
  let step4 fd (id,_,bl,de,dsp) =
    Loc.try3 ?loc:de.de_loc check_lambda_effect fd bl dsp;
    Loc.try2 ?loc:id.id_loc check_user_ps true fd.fun_ps in
  List.iter2 step4 fdl dfdl;
  fdl

and expr_fun ~keep_loc ~strict uloc env (id,gh,bl,de,dsp) =
  let lam, dsp =
    expr_lam ~keep_loc ~strict uloc env gh (binders bl) de dsp in
  if lam.l_spec.c_variant <> [] then Loc.errorm ?loc:id.pre_loc
    "variants are not allowed in a non-recursive definition";
  let lam = (* TODO: the following cannot work in letrec *)
    if Debug.test_noflag implicit_post || dsp.ds_post <> [] ||
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
  (* add invariants *)
  let { l_spec = spec; l_expr = e } = lam in
  let spec = spec_invariant env e.e_syms.syms_pv e.e_vty spec in
  let fd = create_fun_defn id { lam with l_spec = spec } in
  Loc.try3 ?loc:de.de_loc check_lambda_effect fd bl dsp;
  Loc.try2 ?loc:id.pre_loc check_user_ps false fd.fun_ps;
  fd

and expr_lam ~keep_loc ~strict uloc env gh pvl de dsp =
  let env = add_binders env pvl in
  let e = e_ghostify gh (expr ~keep_loc uloc env de) in
  if strict && not gh && e.e_ghost then (* TODO: localize better *)
    Loc.errorm ?loc:de.de_loc "ghost body in a non-ghost function";
  let tyv = ty_of_vty e.e_vty in
  let dsp = dsp env.vsm tyv in
  let spec = spec_of_dspec e.e_effect tyv dsp in
  { l_args = pvl; l_expr = e; l_spec = spec }, dsp

let val_decl ~keep_loc:_ lkn kn vald =
  reunify_regions ();
  val_decl (env_empty lkn kn) vald

let let_defn ~keep_loc lkn kn (id,gh,de) =
  reunify_regions ();
  let e = expr ~keep_loc None (env_empty lkn kn) de in
  let e = e_ghostify gh e in
  if e.e_ghost && not gh then (* TODO: localize better *)
    Loc.errorm ?loc:id.pre_loc "%s must be a ghost variable" id.pre_name;
  create_let_defn id e

let fun_defn ~keep_loc lkn kn dfd =
  reunify_regions ();
  expr_fun ~keep_loc ~strict:true None (env_empty lkn kn) dfd

let rec_defn ~keep_loc lkn kn dfdl =
  reunify_regions ();
  expr_rec ~keep_loc None (env_empty lkn kn) dfdl

let expr ~keep_loc lkn kn de =
  reunify_regions ();
  expr ~keep_loc None (env_empty lkn kn) de
