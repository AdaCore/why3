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
open Ity
open Expr
open Pmodule

(** Program types *)

type dity =
  | Dvar of dvar ref          (* destructible "fresh" type variable *)
  | Dutv of tvsymbol          (* undestructible "user" type variable *)
  | Durg of dity * region     (* undestructible "user" region *)
  | Dapp of itysymbol * dity list * dity list

and dvar =
  | Dval of dity              (* i am equal to dity *)
  | Dpur of dity              (* i am equal to the purified dity *)
  | Dsim of dity * tvsymbol   (* our purified types are equal *)
  | Dreg of dity * tvsymbol   (* unassigned region *)
  | Dtvs of        tvsymbol   (* unassigned variable *)

(* In Dreg and Durg, the dity field is a Dapp of the region's type. *)

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)
type dref = bool list * bool

let dity_of_dvty (argl,res) =
  List.fold_right (fun a d -> Dapp (its_func, [a;d], [])) argl res

let dity_fresh () =
  Dvar (ref (Dtvs (create_tvsymbol (id_fresh "mu"))))

let dity_reg d =
  Dvar (ref (Dreg (d, create_tvsymbol (id_fresh "rho"))))

let rec dity_sim = function
  | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
  | Durg (d,_) -> dity_sim d
  | d -> Dvar (ref (Dsim (d, create_tvsymbol (id_fresh "eta"))))

let rec dity_pur = function
  | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
  | Durg (d,_) -> dity_pur d
  | d -> Dvar (ref (Dpur d))

let app_map fn s tl rl = Dapp (s, List.map fn tl, List.map fn rl)

let dity_of_ity ity =
  let hr = Hreg.create 3 in
  let rec dity ity = match ity.ity_node with
    | Ityvar v -> Dutv v
    | Ityapp (s,tl,rl) -> app_map dity s tl rl
    | Ityreg ({reg_its = s; reg_args = tl; reg_regs = rl} as r) ->
        try Hreg.find hr r with Not_found ->
        let d = dity_reg (app_map dity s tl rl) in
        Hreg.add hr r d; d in
  dity ity

let rec ity_of_dity = function
  | Dutv v -> ity_var v
  | Durg (_,r) -> ity_reg r
  | Dvar {contents = Dval d} -> ity_of_dity d
  | Dvar {contents = Dpur d} -> ity_purify (ity_of_dity d)
  | Dvar ({contents = Dsim (d,_)} as r) ->
      let rec refresh ity = match ity.ity_node with
        | Ityreg {reg_its = s; reg_args = tl} | Ityapp (s,tl,_) ->
            ity_app s (List.map refresh tl) []
        | Ityvar v -> ity_var v in
      let rec dity ity = match ity.ity_node with
        | Ityreg r ->
            Durg (app_map dity r.reg_its r.reg_args r.reg_regs, r)
        | Ityapp (s,tl,rl) -> app_map dity s tl rl
        | Ityvar v -> Dutv v in
      let t = refresh (ity_of_dity d) in
      r := Dval (dity t); t
  | Dvar ({contents = Dreg (Dapp (s,tl,rl) as d,_)} as r) ->
      let reg = create_region (id_fresh "rho") s
        (List.map ity_of_dity tl) (List.map ity_of_dity rl) in
      r := Dval (Durg (d, reg)); ity_reg reg
  | Dvar r ->
      let v = create_tvsymbol (id_fresh "xi") in
      r := Dval (Dutv v); ity_var v
  | Dapp (s,tl,rl) ->
      ity_app_pure s (List.map ity_of_dity tl) (List.map ity_of_dity rl)

(** Destructive type unification *)

let rec occur_check v = function
  | Dvar {contents = (Dval d|Dpur d)} | Durg (d,_) ->
      occur_check v d
  | Dvar {contents = (Dsim (d,u)|Dreg (d,u))} ->
      if tv_equal u v then raise Exit else occur_check v d
  | Dvar {contents = Dtvs u} | Dutv u ->
      if tv_equal u v then raise Exit
  | Dapp (_,dl,_) ->
      List.iter (occur_check v) dl

let rec dity_unify_weak d1 d2 = match d1,d2 with
  | Dvar {contents = (Dval d1|Dpur d1|Dsim (d1,_)|Dreg (d1,_))}, d2
  | d1, Dvar {contents = (Dval d2|Dpur d2|Dsim (d2,_)|Dreg (d2,_))}
  | Durg (d1,_), d2 | d1, Durg (d2,_) ->
      dity_unify_weak d1 d2
  | Dvar {contents = Dtvs u},
    Dvar {contents = Dtvs v} when tv_equal u v ->
      ()
  | Dvar ({contents = Dtvs v} as r), d
  | d, Dvar ({contents = Dtvs v} as r) ->
      occur_check v d;
      r := Dsim (d,v)
  | Dutv u, Dutv v when tv_equal u v ->
      ()
  | Dapp (s1,dl1,_), Dapp (s2,dl2,_) when its_equal s1 s2 ->
      List.iter2 dity_unify_weak dl1 dl2
  | _ -> raise Exit

let dity_app_fresh s dl =
  let mv = List.fold_right2 Mtv.add s.its_ts.ts_args dl Mtv.empty in
  let hr = Hreg.create 3 in
  let rec ity_inst ity = match ity.ity_node with
    | Ityreg r -> reg_inst r
    | Ityvar v -> Mtv.find v mv
    | Ityapp (s,tl,rl) -> app_map ity_inst s tl rl
  and reg_inst ({reg_its = s; reg_args = tl; reg_regs = rl} as r) =
    try Hreg.find hr r with Not_found ->
    let d = dity_reg (app_map ity_inst s tl rl) in
    Hreg.replace hr r d; d in
  Dapp (s, dl, List.map reg_inst s.its_regions)

let rec dity_refresh = function
  | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
  | Durg (d,_) -> dity_refresh d
  | Dutv _ as d -> d
  | Dvar {contents = Dtvs _} -> dity_fresh ()
  | Dapp (s,dl,_) ->
      let d = dity_app_fresh s (List.map dity_refresh dl) in
      if s.its_mutable then dity_reg d else d

let rec dity_unify_asym d1 d2 = match d1,d2 with
  | Durg _, _ -> raise Exit (* we cannot be pure then *)
  | d1, Dvar {contents = (Dval d2|Dpur d2|Dsim (d2,_)|Dreg (d2,_))}
  | d1, Durg (d2,_)
  | Dvar {contents = Dval d1}, d2 ->
      dity_unify_asym d1 d2
  | Dvar {contents = Dpur d1}, d2 ->
      dity_unify_weak d1 d2
  | Dvar ({contents = Dsim (d1,_)} as r), d2 ->
      dity_unify_weak d1 d2;
      r := Dpur d1
  | Dvar ({contents = Dreg (d1,_)} as r), d2 ->
      dity_unify_asym d1 d2;
      r := Dval d1
  | Dvar ({contents = Dtvs u} as r),
    Dvar {contents = Dtvs v} when tv_equal u v ->
      r := Dpur (dity_fresh ())
  | Dvar ({contents = Dtvs v} as r), d ->
      occur_check v d;
      r := Dpur d
  | d (* not a Dvar! *), Dvar ({contents = Dtvs v} as r) ->
      occur_check v d;
      let d2 = dity_refresh d in
      dity_unify_asym d d2;
      r := Dval d2
  | Dutv u, Dutv v when tv_equal u v ->
      ()
  | Dapp (s1,dl1,rl1), Dapp (s2,dl2,rl2) when its_equal s1 s2 ->
      List.iter2 dity_unify_asym dl1 dl2;
      List.iter2 dity_unify_asym rl1 rl2
  | _ -> raise Exit

let rec dity_unify d1 d2 = match d1,d2 with
  | Dvar {contents = Dval d1}, d2 | d1, Dvar {contents = Dval d2} ->
      dity_unify d1 d2
  | Dvar ({contents = Dpur d2}), d1 (* yes, it's d2 on the left *)
  | d1, Dvar ({contents = Dpur d2}) ->
      dity_unify_asym d1 d2
  | Dvar ({contents = Dsim (_,u)}),
    Dvar ({contents = Dsim (_,v)}) when tv_equal u v ->
      ()
  | Dvar ({contents = Dsim (d1,v)} as r), d
  | d, Dvar ({contents = Dsim (d1,v)} as r) ->
      occur_check v d; (* not necessary? *)
      dity_unify_weak d1 d;
      r := Dval d
  | Dvar {contents = Dreg (_,u)},
    Dvar {contents = Dreg (_,v)} when tv_equal u v ->
      ()
  | Dvar ({contents = Dreg (d1,v)} as r),
    ((Dapp _ as d2 | Durg (d2,_) | Dvar {contents = Dreg (d2,_)}) as d)
  | ((Dapp _ as d1 | Durg (d1,_)) as d),
    Dvar ({contents = Dreg (d2,v)} as r) ->
      occur_check v d; (* not necessary! *)
      dity_unify d1 d2;
      r := Dval d
  | Dvar ({contents = Dtvs u}),
    Dvar ({contents = Dtvs v}) when tv_equal u v ->
      ()
  | Dvar ({contents = Dtvs v} as r), d
  | d, Dvar ({contents = Dtvs v} as r) ->
      occur_check v d;
      r := Dval d
  | Dutv u, Dutv v when tv_equal u v ->
      ()
  | Durg (_,r1), Durg (_,r2) when reg_equal r1 r2 ->
      ()
  | Dapp (s1,dl1,rl1), Dapp (s2,dl2,rl2) when its_equal s1 s2 ->
      List.iter2 dity_unify dl1 dl2;
      List.iter2 dity_unify rl1 rl2
  | _ -> raise Exit

(** Built-in types *)

let dity_int  = Dapp (its_int,  [], [])
let dity_real = Dapp (its_real, [], [])
let dity_bool = Dapp (its_bool, [], [])
let dity_unit = Dapp (its_unit, [], [])

(*
let dvty_int  = [], dity_int
let dvty_real = [], dity_real
*)
let dvty_bool = [], dity_bool
let dvty_unit = [], dity_unit

(** Pretty-printing *)

let rprinter =
  let sanitizer = Ident.sanitizer Ident.char_to_lalpha Ident.char_to_alnumus in
  Ident.create_ident_printer [] ~sanitizer

let print_args pr fmt tl = if tl <> [] then
  Format.fprintf fmt "@ %a" (Pp.print_list Pp.space pr) tl

let print_regs pr fmt rl = if rl <> [] then
  Format.fprintf fmt "@ <%a>" (Pp.print_list Pp.comma pr) rl

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_dity pur pri fmt = function
  | Dvar {contents = Dval d} ->
      print_dity pur pri fmt d
  | Dvar {contents = (Dpur d|Dsim (d,_)|Dreg (d,_))}
  | Durg (d,_) when pur ->
      print_dity pur pri fmt d
  | Dvar {contents = Dtvs v} | Dutv v ->
      Pretty.print_tv fmt v
  | Dvar {contents = Dpur d} ->
      Format.fprintf fmt "{%a}" (print_dity true 0) d
  | Dvar {contents = Dsim (d,_)} ->
      Format.fprintf fmt "[%a]" (print_dity true 0) d
  | Dvar {contents = Dreg (Dapp (s,tl,rl),{tv_name = id})}
  | Durg (Dapp (s,tl,rl),{reg_name = id}) ->
      Format.fprintf fmt
        (protect_on (pri > 1 && (tl <> [] || rl <> [])) "%a%a%a@ @@%s")
        Pretty.print_ts_qualified s.its_ts (print_args (print_dity pur 2)) tl
          (print_regs (print_dity pur 0)) rl (Ident.id_unique rprinter id)
  | Dvar {contents = Dreg _} | Durg _ -> assert false
  | Dapp (s,[t1;t2],[]) when its_equal s its_func ->
      Format.fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_dity pur 1) t1 (print_dity pur 0) t2
  | Dapp (s,tl,[]) when is_ts_tuple s.its_ts ->
      Format.fprintf fmt "(%a)" (Pp.print_list Pp.comma (print_dity pur 0)) tl
  | Dapp (s,tl,_) when pur ->
      Format.fprintf fmt (protect_on (pri > 1 && tl <> []) "%a%a")
        Pretty.print_ts_qualified s.its_ts (print_args (print_dity pur 2)) tl
  | Dapp (s,tl,rl) when not s.its_mutable ->
      Format.fprintf fmt
        (protect_on (pri > 1 && (tl <> [] || rl <> [])) "%a%a%a")
        Pretty.print_ts_qualified s.its_ts (print_args (print_dity pur 2)) tl
          (print_regs (print_dity pur 0)) rl
  | Dapp (s,tl,rl) ->
      Format.fprintf fmt
        (protect_on (pri > 1 && (tl <> [] || rl <> [])) "{%a}%a%a")
        Pretty.print_ts_qualified s.its_ts (print_args (print_dity pur 2)) tl
          (print_regs (print_dity pur 0)) rl

let print_dity fmt d = print_dity false 0 fmt d

(* Specialization of symbols *)

let specialize_scheme tvs (argl,res) =
  let hv = Htv.create 3 in
  let rec spec_dity = function
    | Dvar {contents = Dval d} -> spec_dity d
    | Dvar {contents = Dpur d} -> dity_pur (spec_dity d)
    | Dvar {contents = Dsim (d,v)} ->
        (try Htv.find hv v with Not_found ->
        let nd = dity_sim (spec_dity d) in
        Htv.add hv v nd; nd)
    | Dvar {contents = Dreg (d,v)} ->
        (try Htv.find hv v with Not_found ->
        let nd = dity_reg (spec_dity d) in
        Htv.add hv v nd; nd)
    | Dvar {contents = Dtvs v} | Dutv v as d ->
        (try Htv.find hv v with Not_found ->
        (* even if v is frozen, it is polymorphic in its regions *)
        let nd = if Stv.mem v tvs then dity_fresh () else dity_sim d in
        Htv.add hv v nd; nd)
    | Dapp (s,dl,rl) -> app_map spec_dity s dl rl
    | Durg _ as d -> d in
  List.map spec_dity argl, spec_dity res

let spec_ity hv hr frz ity =
  let rec dity ity = match ity.ity_node with
    | Ityreg r ->
        (try Hreg.find hr r with Not_found ->
        let d = app_map dity r.reg_its r.reg_args r.reg_regs in
        let nd = if Mreg.mem r frz.isb_reg then Durg (d,r) else dity_reg d in
        Hreg.add hr r nd; nd)
    | Ityvar v ->
        (try Htv.find hv v with Not_found ->
        let nd = if Mtv.mem v frz.isb_var then Dutv v else dity_fresh () in
        Htv.add hv v nd; nd)
    | Ityapp (s,tl,rl) -> app_map dity s tl rl in
  dity ity

let specialize_single ity =
  spec_ity (Htv.create 3) (Hreg.create 3) (ity_freeze isb_empty ity) ity

let specialize_rs {rs_cty = cty} =
  let hv = Htv.create 3 and hr = Hreg.create 3 in
  let spec ity = spec_ity hv hr cty.cty_freeze ity in
  List.map (fun v -> spec v.pv_ity) cty.cty_args, spec cty.cty_result

let specialize_ls {ls_args = args; ls_value = res} =
  let hv = Htv.create 3 and hr = Hreg.create 3 in
  let spec_val _ ty = spec_ity hv hr isb_empty (ity_of_ty_pure ty) in
  let spec_arg ty = dity_sim (spec_val () ty) in
  List.map spec_arg args, Opt.fold spec_val dity_bool res

type dxsymbol =
  | DElexn of string * dity
  | DEgexn of xsymbol

let specialize_dxs = function
  | DEgexn xs -> specialize_single xs.xs_ity
  | DElexn (_,dity) -> dity

(** Patterns *)

type dpattern = {
  dp_pat  : pre_pattern;
  dp_dity : dity;
  dp_vars : (dity * bool) Mstr.t;
  dp_loc  : Loc.position option;
}

type dpattern_node =
  | DPwild
  | DPvar  of preid * bool
  | DPapp  of rsymbol * dpattern list
  | DPas   of dpattern * preid * bool
  | DPor   of dpattern * dpattern
  | DPcast of dpattern * dity

(** Specifications *)

type ghost = bool

type dbinder = preid option * ghost * dity

type register_old = string -> pvsymbol -> pvsymbol

type 'a later = pvsymbol Mstr.t -> xsymbol Mstr.t -> register_old -> 'a
  (* specification terms are parsed and typechecked after the program
     expressions, when the types of locally bound program variables are
     already established. *)

type dspec_final = {
  ds_pre     : term list;
  ds_post    : (pvsymbol * term) list;
  ds_xpost   : (pvsymbol * term) list Mxs.t;
  ds_reads   : pvsymbol list;
  ds_writes  : term list;
  ds_diverge : bool;
  ds_partial : bool;
  ds_checkrw : bool;
}

type dspec = ity -> dspec_final
  (* Computation specification is also parametrized by the result type.
     All vsymbols in the postcondition clauses in the [ds_post] field
     must have this type. All vsymbols in the exceptional postcondition
     clauses must have the type of the corresponding exception. *)

let old_label = "'Old"

(** Expressions *)

type dinvariant = term list

type dexpr = {
  de_node : dexpr_node;
  de_dvty : dvty;
  de_loc  : Loc.position option;
}

and dexpr_node =
  | DEvar of string * dvty * dref
  | DEsym of prog_symbol
  | DEconst of Number.constant * dity
  | DEapp of dexpr * dexpr
  | DEfun of dbinder list * dity * mask * dspec later * dexpr
  | DEany of dbinder list * dity * mask * dspec later
  | DElet of dlet_defn * dexpr
  | DErec of drec_defn * dexpr
  | DEnot of dexpr
  | DEand of dexpr * dexpr
  | DEor of dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEmatch of dexpr * dreg_branch list * dexn_branch list
  | DEassign of (dexpr * rsymbol * dexpr) list
  | DEwhile of dexpr * dinvariant later * variant list later * dexpr
  | DEfor of preid * dexpr * for_direction * dexpr * dinvariant later * dexpr
  | DEraise of dxsymbol * dexpr
  | DEghost of dexpr
  | DEexn of preid * dity * mask * dexpr
  | DEoptexn of preid * dity * mask * dexpr
  | DEassert of assertion_kind * term later
  | DEpure of term later * dity
  | DEvar_pure of string * dvty * dref
  | DEls_pure of lsymbol * bool
  | DEpv_pure of pvsymbol
  | DEabsurd
  | DEtrue
  | DEfalse
  | DElabel of preid * dexpr
  | DEcast of dexpr * dity
  | DEuloc of dexpr * Loc.position
  | DEattr of dexpr * Sattr.t

and dreg_branch = dpattern * dexpr

and dexn_branch = dxsymbol * dpattern * dexpr

and dlet_defn = preid * ghost * rs_kind * dexpr

and drec_defn = { fds : dfun_defn list }

and dfun_defn = preid * ghost * rs_kind * dbinder list *
  dity * mask * dspec later * variant list later * dexpr

(** Unification tools *)

let dity_unify_app ls fn (l1: 'a list) (l2: dity list) =
  try List.iter2 fn l1 l2 with Invalid_argument _ ->
    raise (BadArity (ls, List.length l1))

let dvar_expected_type {pre_loc = loc} dv_dity dity =
  try dity_unify dv_dity dity with Exit -> Loc.errorm ?loc
    "This variable has type %a,@ but is expected to have type %a"
    print_dity dv_dity print_dity dity

let dpat_expected_type {dp_dity = dp_dity; dp_loc = loc} dity =
  try dity_unify dp_dity dity with Exit -> Loc.errorm ?loc
    "This pattern has type %a,@ but is expected to have type %a"
    print_dity dp_dity print_dity dity

let dexpr_expected_type {de_dvty = dvty; de_loc = loc} dity =
  let res = dity_of_dvty dvty in
  try dity_unify res dity with Exit -> Loc.errorm ?loc
    "This expression has type %a,@ but is expected to have type %a"
    print_dity res print_dity dity

let dexpr_expected_type_weak {de_dvty = dvty; de_loc = loc} dity =
  let res = dity_of_dvty dvty in
  try dity_unify_weak res dity with Exit -> Loc.errorm ?loc
    "This expression has type %a,@ but is expected to have type %a"
    print_dity res print_dity dity

(** Environment *)

type denv = {
  frozen : dity list;
  locals : (bool * Stv.t option * dvty * dref) Mstr.t;
  excpts : dxsymbol Mstr.t
}

let denv_names d = Mstr.domain d.locals

let denv_empty = { frozen = []; locals = Mstr.empty; excpts = Mstr.empty }

let is_frozen frozen v =
  try List.iter (occur_check v) frozen; false with Exit -> true

let freeze_dvty frozen (argl,res) =
  let rec add l = function
    | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
    | Durg (d,_) -> add l d
    | Dvar {contents = Dtvs _}
    | Dutv _ as d -> d :: l
    | Dapp (_,tl,_) -> List.fold_left add l tl in
  List.fold_left add (add frozen res) argl

let free_vars frozen (argl,res) =
  let rec add s = function
    | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
    | Durg (d,_) -> add s d
    | Dvar {contents = Dtvs v} | Dutv v ->
        if is_frozen frozen v then s else Stv.add v s
    | Dapp (_,tl,_) -> List.fold_left add s tl in
  List.fold_left add (add Stv.empty res) argl

let denv_add_exn {frozen = fz; locals = ls; excpts = xs} id dity =
  let xs = Mstr.add id.pre_name (DElexn (id.pre_name, dity)) xs in
  { frozen = freeze_dvty fz ([], dity); locals = ls; excpts = xs }

let denv_add_mono {frozen = fz; locals = ls; excpts = xs} id dvty dref =
  let ls = Mstr.add id.pre_name (false, None, dvty, dref) ls in
  { frozen = freeze_dvty fz dvty; locals = ls; excpts = xs }

let denv_add_poly {frozen = fz; locals = ls; excpts = xs} id dvty dref =
  let fvs = free_vars fz dvty in
  let ls = Mstr.add id.pre_name (false, Some fvs, dvty, dref) ls in
  { frozen = fz; locals = ls; excpts = xs }

let denv_add_rec_mono {frozen = fz; locals = ls; excpts = xs} id dvty dref =
  let ls = Mstr.add id.pre_name (false, Some Stv.empty, dvty, dref) ls in
  { frozen = freeze_dvty fz dvty; locals = ls; excpts = xs }

let denv_add_rec_poly {frozen = fz; locals = ls; excpts = xs} fz0 id dvty dref =
  let fvs = free_vars fz0 dvty in
  let ls = Mstr.add id.pre_name (false, Some fvs, dvty, dref) ls in
  { frozen = fz; locals = ls; excpts = xs }

let denv_add_rec denv fz0 id ((argl,res) as dvty) dref =
  let rec is_explicit = function
    | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
    | Durg (d,_) -> is_explicit d
    | Dvar {contents = Dtvs _} -> false
    | Dutv _ -> true
    | Dapp (_,tl,_) -> List.for_all is_explicit tl in
  if List.for_all is_explicit argl && is_explicit res
  then denv_add_rec_poly denv fz0 id dvty dref
  else denv_add_rec_mono denv id dvty dref

let attr_dref attrs = Sattr.mem Pmodule.ref_attr attrs

let bl_dref bl =
  let check = function
    | Some id,_,_ -> attr_dref id.pre_attrs
    | _ -> false in
  List.map check bl

let bl_type bl = List.map (fun (_,_,t) -> t) bl

let pv_dref pv = attr_dref pv.pv_vs.vs_name.id_attrs

let id_nref {pre_loc = loc; pre_attrs = attrs} =
  if attr_dref attrs then Loc.errorm ?loc
    "reference markers are only admitted over program variables";
  false

let id_dref id dity =
  if attr_dref id.pre_attrs then begin
    let dity_ref = dity_reg (Dapp (its_ref, [dity_fresh ()], [])) in
    dvar_expected_type id dity dity_ref;
    true
  end else
    false

let argl_dref ({de_dvty = argl,_} as de) =
  let rec cut dr acc = match dr, acc with
    | dr, [] -> assert (List.length dr = List.length argl); dr
    | _::dr, _::acc -> cut dr acc
    | _, _ -> List.map Util.ffalse argl in
  let rec deapp acc de = match de.de_node with
    | DEvar (_,_,(dr,_)) (* no DEvar_pure|DEls_pure *) -> cut dr acc
    | DEsym (RS rs) -> cut (List.map pv_dref rs.rs_cty.cty_args) acc
    | DEfun (bl,_,_,_,_) | DEany (bl,_,_,_) -> cut (bl_dref bl) acc
    | DEapp (de,d) -> deapp (d::acc) de
    | DEuloc (de,_) | DEattr (de,_) | DEcast (de,_)
    | DElet (_,de) | DErec (_,de) | DElabel (_,de)
    | DEexn (_,_,_,de) | DEoptexn (_,_,_,de)
    | DEghost de -> deapp acc de
    | _ -> List.map Util.ffalse argl in
  deapp [] de

let denv_add_var denv id dity =
  denv_add_mono denv id ([], dity) ([], id_dref id dity)

let denv_add_for_index denv id dvty =
  let dvty = [], dity_of_dvty dvty in
  let dref = [], id_dref id (snd dvty) in
  let { frozen = fz; locals = ls; excpts = xs } = denv in
  let ls = Mstr.add id.pre_name (true, None, dvty, dref) ls in
  { frozen = freeze_dvty fz dvty; locals = ls; excpts = xs }

let denv_add_let denv (id,_,_,({de_dvty = (argl,res as dvty)} as de)) =
  let dref = if argl = [] then [], id_dref id res
                else argl_dref de, id_nref id in
  if argl = [] then denv_add_mono denv id dvty dref else
  let rec is_value de = match de.de_node with
    | DEghost de | DEuloc (de,_) | DEattr (de,_) -> is_value de
    | DEvar _ | DEsym _ | DEls_pure _ | DEfun _ | DEany _ -> true
    | _ -> false in
  if is_value de then denv_add_poly denv id dvty dref
                 else denv_add_mono denv id dvty dref

let denv_add_args {frozen = fz; locals = ls; excpts = xs} bl =
  let l = List.fold_left (fun l (_,_,t) -> t::l) fz bl in
  let add s (id,_,t) = match id with
    | Some ({pre_name = n} as id) ->
        let dvty = [], t and dref = [], id_dref id t in
        Mstr.add_new (Dterm.DuplicateVar n) n (false, None, dvty, dref) s
    | None -> s in
  let s = List.fold_left add Mstr.empty bl in
  { frozen = l; locals = Mstr.set_union s ls; excpts = xs }

let denv_add_pat {frozen = fz; locals = ls; excpts = xs} dp dity =
  dpat_expected_type dp dity;
  let l = Mstr.fold (fun _ (t,_) l -> t::l) dp.dp_vars fz in
  let s = Mstr.map (fun (t,d) -> false, None, ([],t), ([],d)) dp.dp_vars in
  { frozen = l; locals = Mstr.set_union s ls; excpts = xs }

let denv_add_expr_pat denv dp de =
  denv_add_pat denv dp (dity_of_dvty de.de_dvty)

let denv_add_exn_pat denv dp dxs =
  denv_add_pat denv dp (specialize_dxs dxs)

let mk_node n = function
  | _, Some tvs, dvty, dref -> DEvar (n, specialize_scheme tvs dvty, dref)
  | _, None,     dvty, dref -> DEvar (n, dvty, dref)

let denv_get denv n =
  mk_node n (Mstr.find_exn (Dterm.UnboundVar n) n denv.locals)

let denv_get_opt denv n =
  Opt.map (mk_node n) (Mstr.find_opt n denv.locals)

let mk_node_pure n = function
  | _, Some tvs, dvty, dref -> DEvar_pure (n, specialize_scheme tvs dvty, dref)
  | _, None,     dvty, dref -> DEvar_pure (n, dvty, dref)

let denv_get_pure denv n =
  mk_node_pure n (Mstr.find_exn (Dterm.UnboundVar n) n denv.locals)

let denv_get_pure_opt denv n =
  Opt.map (mk_node_pure n) (Mstr.find_opt n denv.locals)

exception UnboundExn of string

let denv_get_exn denv n = Mstr.find_exn (UnboundExn n) n denv.excpts

let denv_get_exn_opt denv n = Mstr.find_opt n denv.excpts

let denv_pure denv get_dty =
  let ht = Htv.create 3 in
  let hi = Hint.create 3 in
  let rec fold = function
    | Dvar {contents = (Dval d|Dpur d|Dsim (d,_)|Dreg (d,_))}
    | Durg (d,_) -> fold d
    | Dvar {contents = Dtvs v} as d ->
        begin try fst (Htv.find ht v) with Not_found ->
        let f = Dterm.dty_fresh () in Htv.add ht v (f,d); f end
    | Dapp (s,dl,_) -> Dterm.dty_app s.its_ts (List.map fold dl)
    | Dutv v -> Dterm.dty_var v in
  let add n (idx, _, dvty, dref) =
    let dity = if idx then dity_int else dity_of_dvty dvty in
    let dt = Dterm.DTvar (n, fold dity) in
    if dref = ([], true) then
      let dt = Dterm.dterm Coercion.empty dt in
      let dt = Dterm.DTattr (dt, Sattr.singleton Pmodule.ref_attr) in
      let dt = Dterm.dterm Coercion.empty dt in
      Dterm.DTapp (ls_ref_proj, [dt])
    else dt in
  let dty = get_dty (Mstr.mapi add denv.locals) in
  Htv.iter (fun v (f,_) ->
    try Dterm.dty_match f (ty_var v) with Exit -> ()) ht;
  let fnS s dl = dity_app_fresh (restore_its s) dl in
  let fnV v = try snd (Htv.find ht v) with Not_found -> Dutv v in
  let fnI i = try Hint.find hi i with Not_found ->
    let d = dity_fresh () in Hint.add hi i d; d in
  dity_pur (Dterm.dty_fold fnS fnV fnI dty)

(** Generation of letrec blocks *)

type pre_fun_defn = preid * ghost * rs_kind * dbinder list *
  dity * mask * (denv -> dspec later * variant list later * dexpr)

exception DupId of preid

let drec_defn ({frozen = frz} as denv0) prel =
  if prel = [] then invalid_arg "Dexpr.drec_defn: empty function list";
  let add s (id,_,_,_,_,_,_) = Sstr.add_new (DupId id) id.pre_name s in
  let _ = try List.fold_left add Sstr.empty prel with DupId id ->
    Loc.errorm ?loc:id.pre_loc "duplicate function name %s" id.pre_name in
  let add denv (id,_,_,bl,res,_,_) =
    if bl = [] then invalid_arg "Dexpr.drec_defn: empty argument list";
    denv_add_rec denv frz id (bl_type bl, res) (bl_dref bl, id_nref id) in
  let denv1 = List.fold_left add denv0 prel in
  let parse (id,gh,pk,bl,res,msk,pre) =
    let dsp, dvl, de = pre denv1 in
    dexpr_expected_type de res;
    (id,gh,pk,bl,res,msk,dsp,dvl,de) in
  let fdl = List.map parse prel in
  let add denv (id,_,_,bl,res,_,_,_,_) =
    (* in case we linked some polymorphic type var to the outer context *)
    let check tv = if is_frozen frz tv then Loc.errorm ?loc:id.pre_loc
      "This function is expected to be polymorphic in type variable %a"
      Pretty.print_tv tv in
    begin match Mstr.find_opt id.pre_name denv1.locals with
    | Some (_, Some tvs, _, _) -> Stv.iter check tvs
    | Some (_, None, _, _) | None -> assert false end;
    denv_add_poly denv id (bl_type bl, res) (bl_dref bl, false) in
  List.fold_left add denv0 fdl, { fds = fdl }

(** Constructors *)

let dpattern ?loc node =
  let mk_dpat pre dity vars =
    { dp_pat = pre; dp_dity = dity; dp_vars = vars; dp_loc = loc } in
  let dpat = function
    | DPwild ->
        mk_dpat PPwild (dity_fresh ()) Mstr.empty
    | DPvar (id,gh) ->
        let dity = dity_fresh () in
        let vars = Mstr.singleton id.pre_name (dity, id_dref id dity) in
        mk_dpat (PPvar (id,gh)) dity vars
    | DPapp ({rs_logic = RLls ls} as rs, dpl) when ls.ls_constr > 0 ->
        let argl, res = specialize_rs rs in
        dity_unify_app ls dpat_expected_type dpl argl;
        let join n _ _ = raise (Dterm.DuplicateVar n) in
        let add acc dp = Mstr.union join acc dp.dp_vars in
        let vars = List.fold_left add Mstr.empty dpl in
        let ppl = List.map (fun dp -> dp.dp_pat) dpl in
        mk_dpat (PPapp (rs, ppl)) res vars
    | DPapp (rs,_) ->
        raise (ConstructorExpected rs);
    | DPor (dp1,dp2) ->
        dpat_expected_type dp2 dp1.dp_dity;
        let join n (dity1,dref1) (dity2,dref2) =
          if dref1 <> dref2 then Loc.errorm ?loc
            "Variable %s is used with different ref statuses" n;
          try dity_unify dity1 dity2; Some (dity1,dref1)
          with Exit -> Loc.errorm ?loc
            "Variable %s has type %a,@ but is expected to have type %a"
            n print_dity dity1 print_dity dity2 in
        let vars = Mstr.union join dp1.dp_vars dp2.dp_vars in
        mk_dpat (PPor (dp1.dp_pat, dp2.dp_pat)) dp1.dp_dity vars
    | DPas (dp, ({pre_name = n} as id), gh) ->
        let exn = Dterm.DuplicateVar n in
        let { dp_pat = pat; dp_dity = dity; dp_vars = vars } = dp in
        let vars = Mstr.add_new exn n (dity, id_dref id dity) vars in
        mk_dpat (PPas (pat, id, gh)) dity vars
    | DPcast (dp, dity) ->
        dpat_expected_type dp dity;
        dp
  in
  Loc.try1 ?loc dpat node

let to_deref = function
  | DEvar (_,_,([],deref))
  | DEvar_pure (_,_,([],deref)) -> deref
  | DEsym (PV pv)
  | DEpv_pure pv -> pv_dref pv
  | _ -> false

let rec undereference de = match de.de_node with
  | DEuloc (de,l) -> { de with de_node = DEuloc (undereference de, l) }
  | DEattr (de,a) -> { de with de_node = DEattr (undereference de, a) }
  | DEcast (de,_) -> undereference de (* already unified *)
  | DEapp ({de_node = DEsym (RS rs)}, de)
    when rs_equal rs rs_ref_proj
      && to_deref de.de_node -> de
  | _ -> raise Not_found

let dexpr ?loc node =
  let get_dvty = function
    | DEvar (_,dvty,_) ->
        dvty
    | DEvar_pure (_,dvty,_) ->
        let dt = dity_fresh () in
        dity_unify_asym dt (dity_of_dvty dvty);
        [], dt
    | DEsym (PV pv) ->
        [], specialize_single pv.pv_ity
    | DEsym (RS rs) ->
        specialize_rs rs
    | DEsym (OO ss) ->
        let dt = dity_fresh () in
        let rs = Srs.choose ss in
        let ot = overload_of_rs rs in
        let res = match ot with
          | SameType -> dt
          | FixedRes ity -> dity_of_ity ity
          | NoOver -> assert false (* impossible *) in
        List.map (fun _ -> dt) rs.rs_cty.cty_args, res
    | DEls_pure (ls,_) ->
        specialize_ls ls
    | DEpv_pure pv ->
        [], specialize_single (ity_purify pv.pv_ity)
    | DEconst (_, ity) -> [],ity
    | DEapp ({de_dvty = (arg::argl, res)}, de2) ->
        dexpr_expected_type de2 arg;
        argl, res
    | DEapp ({de_dvty = ([],res)} as de1, de2) ->
        let f,a,r = match specialize_rs rs_func_app with
          | [f;a],r -> f,a,r | _ -> assert false in
        begin try dity_unify res f with Exit ->
          let rec down n de = match de.de_node with
            | DEapp (de,_) -> down (succ n) de
            | _ when n = 0 -> Loc.errorm ?loc:de.de_loc
                "This expression has type %a,@ it cannot be applied"
                print_dity (dity_of_dvty de.de_dvty)
            | _ -> Loc.errorm ?loc:de.de_loc
                "This expression has type %a,@ but is applied to %d arguments"
                print_dity (dity_of_dvty de.de_dvty) (succ n) in
          down 0 de1
        end;
        dexpr_expected_type de2 a;
        [], r
    | DEfun (bl,res,_,_,de) ->
        dexpr_expected_type de res;
        bl_type bl, res
    | DEany (bl,res,_,_) ->
        bl_type bl, res
    | DElet (_,de)
    | DErec (_,de) ->
        de.de_dvty
    | DEnot de ->
        dexpr_expected_type de dity_bool;
        dvty_bool
    | DEand (de1,de2)
    | DEor (de1,de2) ->
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 dity_bool;
        dvty_bool
    | DEif (de1,de2,de3) ->
        let res = dity_fresh () in
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 res;
        dexpr_expected_type de3 res;
        [], res
    | DEmatch (_,[],[]) ->
        invalid_arg "Dexpr.dexpr: empty branch list in DEmatch"
    | DEmatch (de,bl,xl) ->
        let res = dity_fresh () in
        if bl = [] then dexpr_expected_type de res;
        List.iter (fun (_,de) -> dexpr_expected_type de res) bl;
        List.iter (fun (_,_,de) -> dexpr_expected_type de res) xl;
        [], res
    | DEassign al ->
        List.iter (fun (de1,rs,de2) ->
          let argl, res = specialize_rs rs in
          let ls = match rs.rs_logic with RLls ls -> ls
            | _ -> invalid_arg "Dexpr.dexpr: not a field" in
          dity_unify_app ls dexpr_expected_type [de1] argl;
          dexpr_expected_type_weak de2 res) al;
        dvty_unit
    | DEwhile (de1,_,_,de2) ->
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 dity_unit;
        dvty_unit
    | DEfor (_,de_from,_,de_to,_,de) ->
        let bty = dity_fresh () in
        dexpr_expected_type de_from bty;
        dexpr_expected_type de_to bty;
        dexpr_expected_type de dity_unit;
        dvty_unit
    | DEraise (xs,de) ->
        dexpr_expected_type de (specialize_dxs xs);
        [], dity_fresh ()
    | DEexn (_,_,_,de)
    | DEghost de ->
        de.de_dvty
    | DEassert _ ->
        dvty_unit
    | DEpure (_, dity) ->
        [], dity
    | DEabsurd ->
        [], dity_fresh ()
    | DEtrue
    | DEfalse ->
        dvty_bool
    | DEoptexn (_,dity,_,de) ->
        dexpr_expected_type de dity;
        [], dity
    | DEcast (de,dity) ->
        dexpr_expected_type de dity;
        de.de_dvty
    | DElabel (_,de)
    | DEuloc (de,_)
    | DEattr (de,_) ->
        de.de_dvty in
  (* suppress dereference if needed *)
  let node = match node with
    | DEapp (e,d) ->
        begin try
          let r = undereference d in
          match argl_dref e with
          | true::_ -> DEapp (e,r)
          | _ -> node
        with Not_found -> node end
    | _ -> node in
  (* dereference if needed *)
  let node = if not (to_deref node) then node else
    let de = { de_node = node;
               de_dvty = get_dvty node;
               de_loc  = loc } in
    let dr = { de_node = DEsym (RS rs_ref_proj);
               de_dvty = specialize_rs rs_ref_proj;
               de_loc  = loc } in
    DEapp (dr, de) in
  (* infer types *)
  let dvty = Loc.try1 ?loc get_dvty node in
  { de_node = node; de_dvty = dvty; de_loc = loc }

(** Final stage *)

(** Binders *)

let binders ghost bl =
  let sn = ref Sstr.empty in
  let binder (id, gh, dity) =
    let id = match id with
      | Some ({pre_name = n} as id) ->
          let exn = match id.pre_loc with
            | Some loc -> Loc.Located (loc, Dterm.DuplicateVar n)
            | None -> Dterm.DuplicateVar n in
          sn := Sstr.add_new exn n !sn; id
      | None -> id_fresh "_" in
    create_pvsymbol id ~ghost:(ghost || gh) (ity_of_dity dity) in
  List.map binder bl

(** Specifications *)

let to_fmla f = match f.t_ty with
  | None -> f
  | Some ty when ty_equal ty ty_bool -> t_equ f t_bool_true
  | _ -> Loc.error ?loc:f.t_loc Dterm.FmlaExpected

let create_assert = to_fmla

let create_invariant pl = List.map to_fmla pl

let create_post ity ql = List.map (fun (v,f) ->
  ity_equal_check ity v.pv_ity; Ity.create_post v.pv_vs (to_fmla f)) ql

let create_xpost xql = Mxs.mapi (fun xs ql -> create_post xs.xs_ity ql) xql

(** User effects *)

let rec effect_of_term t =
  let quit () = Loc.errorm ?loc:t.t_loc "unsupported effect expression" in
  match t.t_node with
  | Tapp (fs, [ta]) ->
      let v, ity, fa = effect_of_term ta in
      let ity = match fa with
        | Some {rs_cty = {cty_args = [arg]; cty_result = res}} ->
            ity_full_inst (ity_match isb_empty arg.pv_ity ity) res
        | Some _ -> assert false
        | None -> ity in
      begin try match ity.ity_node, restore_rs fs with
        | Ityreg {reg_its = ts}, ({rs_field = Some f} as rs)
          when List.exists (pv_equal f) ts.its_mfields -> v, ity, Some rs
        | _, {rs_cty={cty_args=[arg]; cty_result=res; cty_freeze=frz}} ->
            v, ity_full_inst (ity_match frz arg.pv_ity ity) res, None
        | _ -> quit () with Not_found -> quit () end
  | Tvar v ->
      let v = try restore_pv v with Not_found -> quit () in
      v, v.pv_ity, None
  | _ -> quit ()

let effect_of_dspec dsp =
  let pvs = Spv.of_list dsp.ds_reads in
  let add_write (l,eff) t = match effect_of_term t with
    | v, {ity_node = Ityreg reg}, fd ->
        let fs = match fd with
          | Some fd -> Spv.singleton (Opt.get fd.rs_field)
          | None -> Spv.of_list reg.reg_its.its_mfields in
        if not reg.reg_its.its_private && Spv.is_empty fs then
          Loc.errorm ?loc:t.t_loc "mutable expression expected";
        let rd = Spv.singleton v and wr = Mreg.singleton reg fs in
        let e = Loc.try2 ?loc:t.t_loc eff_write rd wr in
        (e,t)::l, eff_union_par eff e
    | _ ->
        Loc.errorm ?loc:t.t_loc "mutable expression expected" in
  let wl, eff = List.fold_left add_write ([], eff_read pvs) dsp.ds_writes in
  let eff = Mxs.fold (fun xs _ eff -> eff_raise eff xs) dsp.ds_xpost eff in
  let eff = if dsp.ds_partial then eff_partial eff else eff in
  let eff = if dsp.ds_diverge then eff_diverge eff else eff in
  wl, eff

(* TODO: add warnings for empty postconditions (anywhere)
    and empty exceptional postconditions (toplevel). *)
let check_spec inr dsp ecty ({e_loc = loc} as e) =
  let bad_read  reff eff = not (Spv.subset reff.eff_reads  eff.eff_reads) in
  let bad_write weff eff = not (Mreg.submap (fun _ s1 s2 -> Spv.subset s1 s2)
                                           weff.eff_writes eff.eff_writes) in
  let bad_raise xeff eff = not (Sxs.subset xeff.eff_raises eff.eff_raises) in
  (* computed effect vs user effect *)
  let uwrl, ue = effect_of_dspec dsp in
  let ucty = create_cty ecty.cty_args ecty.cty_pre ecty.cty_post
    ecty.cty_xpost ecty.cty_oldies ue ecty.cty_result in
  let ueff = ucty.cty_effect and eeff = ecty.cty_effect in
  let check_ue = not inr and check_rw = dsp.ds_checkrw in
  (* check that every user effect actually happens. We omit this
     for local functions inside recursive functions because if
     they call the parent function, they may have more effects
     than we know at this point: those will only be known after
     we finish constructing the parent function. TODO: make an
     effort to only disable the check for local functions that
     actually call their parent. *)
  if check_ue && bad_read ueff eeff then Loc.errorm ?loc
    "variable@ %a@ does@ not@ occur@ in@ this@ expression"
    Pretty.print_vs (Spv.choose (Spv.diff ueff.eff_reads eeff.eff_reads)).pv_vs;
  if check_ue && bad_write ueff eeff then List.iter (fun (weff,t) ->
    if bad_write weff eeff then Loc.errorm ?loc:t.t_loc
      "this@ write@ effect@ does@ not@ happen@ in@ the@ expression") uwrl;
  if check_ue && bad_raise ueff eeff then Loc.errorm ?loc
    "this@ expression@ does@ not@ raise@ exception@ %a"
    print_xs (Sxs.choose (Sxs.diff ueff.eff_raises eeff.eff_raises));
  if check_ue && diverges ueff.eff_oneway && not (diverges eeff.eff_oneway)
    then Loc.errorm ?loc "this@ expression@ does@ not@ diverge";
  if check_ue && partial ueff.eff_oneway && total eeff.eff_oneway
    then Loc.errorm ?loc "this@ expression@ does@ not@ diverge@ or@ fail";
  (* check that every computed effect is listed *)
  if check_rw && bad_read eeff ueff then Loc.errorm ?loc
    "this@ expression@ depends@ on@ variable@ %a,@ \
      which@ is@ left@ out@ in@ the@ specification"
    Pretty.print_vs (Spv.choose (Spv.diff eeff.eff_reads ueff.eff_reads)).pv_vs;
  if check_rw && bad_write eeff ueff then
    Loc.errorm ?loc:(e_locate_effect (fun eff -> bad_write eff ueff) e)
      "this@ expression@ produces@ an@ unlisted@ write@ effect";
  if ecty.cty_args <> [] && bad_raise eeff ueff then Sxs.iter (fun xs ->
    Loc.errorm ?loc:(e_locate_effect (fun eff -> Sxs.mem xs eff.eff_raises) e)
      "this@ expression@ raises@ unlisted@ exception@ %a"
      print_xs xs) (Sxs.diff eeff.eff_raises ueff.eff_raises)

let check_aliases recu c =
  let rds_regs = c.cty_freeze.isb_reg in
  let report r _ _ =
    if Mreg.mem r rds_regs then
      let spv = Spv.filter
        (fun v -> ity_r_occurs r v.pv_ity) (cty_reads c) in
      if not (Spv.is_empty spv) then Loc.errorm
        "The type of this function contains an alias with \
        external variable %a" print_pv (Spv.choose spv);
      let sxs = Sxs.filter
        (fun xs -> ity_r_occurs r xs.xs_ity) (c.cty_effect.eff_raises) in
      Loc.errorm
        "The type of this function contains an alias with \
        external local exception %a" print_xs (Sxs.choose sxs)
    else Loc.errorm "The type of this function contains an alias" in
  (* we allow the value in a non-recursive function to contain
     regions coming the function's arguments or from the context.
     It is safe and sometimes useful to write a function around
     a constructor or a projection. For recursive functions, we
     impose the full non-alias discipline, to ensure the safety
     of region polymorphism (see add_rec_mono). We do not track
     aliases inside the type of an argument or a result, which
     may break the type inference, but we have a safety net
     type checking in Expr. *)
  let add_ity regs ity =
    let frz = ity_freeze isb_empty ity in
    Mreg.union report regs frz.isb_reg in
  let add_arg regs v = add_ity regs v.pv_ity in
  let regs = List.fold_left add_arg rds_regs c.cty_args in
  if recu then ignore (add_ity regs c.cty_result)

let check_fun inr rsym dsp ce =
  let c,e = match ce with
    | { c_node = Cfun e; c_cty = c } -> c,e
    | _ -> invalid_arg "Dexpr.check_fun" in
  let c = match rsym with
    | Some s -> s.rs_cty
    | None -> c in
  check_spec inr dsp c e;
  check_aliases (rsym <> None) c

(** Environment *)

type env = {
  rsm : rsymbol Mstr.t;
  pvm : pvsymbol Mstr.t;
  xsm : xsymbol Mstr.t;
  old : (pvsymbol Mstr.t * (let_defn * pvsymbol) Hpv.t) Mstr.t;
  idx : pvsymbol Mpv.t; (* external-to-internal loop indexes *)
  ghs : bool; (* we are under DEghost or in a ghost function *)
  lgh : bool; (* we are under let ghost c = <cexp> *)
  cgh : bool; (* we are under DEghost in a cexp *)
  inr : bool; (* we are inside a recursive function *)
  ugh : bool; (* suppress the warning on Cpur *)
}

let env_empty = {
  rsm = Mstr.empty;
  pvm = Mstr.empty;
  xsm = Mstr.empty;
  old = Mstr.empty;
  idx = Mpv.empty;
  ghs = false;
  lgh = false;
  cgh = false;
  inr = false;
  ugh = false;
}

exception UnboundLabel of string

let find_old pvm (ovm,old) v =
  if v.pv_ity.ity_pure then v else
  let n = v.pv_vs.vs_name.id_string in
  (* if v is top-level, both ov and pv are None.
     If v is local, ov and pv must be equal to v.
     If they are not equal, then v is defined under the label,
     so we return v and do not register an "oldie" for it. *)
  let ov = Mstr.find_opt n ovm in
  let pv = Mstr.find_opt n pvm in
  if not (Opt.equal pv_equal ov pv) then v
  else match Hpv.find_opt old v with
    | Some (_,o) -> o
    | None ->
        let e = e_pure (t_var v.pv_vs) in
        let id = id_clone v.pv_vs.vs_name in
        let ld = let_var id ~ghost:true e in
        Hpv.add old v ld; snd ld

let register_old env l =
  let old = Mstr.find_exn (UnboundLabel l) l env.old in
  fun v -> find_old env.pvm old v

let get_later env later =
  let pvm = if Mpv.is_empty env.idx then env.pvm else
    Mstr.map (fun v -> Mpv.find_def v v env.idx) env.pvm in
  later pvm env.xsm (register_old env)

let add_label ({pvm = pvm; old = old} as env) l =
  let ht = Hpv.create 3 in
  { env with old = Mstr.add l (pvm, ht) old }, ht

let rebase_old {pvm = pvm} preold old fvs =
  let rebase v (_,{pv_vs = o}) sbs =
    if not (Mvs.mem o fvs) then sbs else match preold with
      | Some preold ->
          Mvs.add o (t_var (find_old pvm preold v).pv_vs) sbs
      | None -> raise (UnboundLabel old_label) in
  Hpv.fold rebase old Mvs.empty

let rebase_pre env preold old pl =
  let pl = List.map to_fmla pl in
  let fvs = List.fold_left t_freevars Mvs.empty pl in
  let sbs = rebase_old env preold old fvs in
  List.map (t_subst sbs) pl

let rebase_variant env preold old varl =
  let add s (t,_) = t_freevars s t in
  let fvs = List.fold_left add Mvs.empty varl in
  let sbs = rebase_old env preold old fvs in
  let conv (t,rel) = t_subst sbs t, rel in
  List.map conv varl

let get_oldies old =
  Hpv.fold (fun v (_,o) sbs -> Mpv.add o v sbs) old Mpv.empty

let add_rsymbol ({rsm = rsm; pvm = pvm} as env) rs =
  let n = rs.rs_name.id_string in
  let pvm = match rs.rs_logic with
    | RLpv pv -> Mstr.add n pv pvm
    | _ -> pvm in
  { env with rsm = Mstr.add n rs rsm; pvm = pvm }

let add_pvsymbol ({pvm = pvm} as env) pv =
  let n = pv.pv_vs.vs_name.id_string in
  { env with pvm = Mstr.add n pv pvm }

let add_pv_map ({pvm = pvm} as env) vm =
  { env with pvm = Mstr.set_union vm pvm }

let add_binders env pvl = List.fold_left add_pvsymbol env pvl

let add_xsymbol ({xsm = xsm} as env) xs =
  { env with xsm = Mstr.add xs.xs_name.id_string xs xsm }

(** Abstract values *)

let cty_of_spec env bl mask dsp dity =
  let ity = ity_of_dity dity in
  let bl = binders env.ghs bl in
  let env = add_binders env bl in
  let preold = Mstr.find_opt old_label env.old in
  let env, old = add_label env old_label in
  let dsp = get_later env dsp ity in
  let _, eff = effect_of_dspec dsp in
  let eff = eff_ghostify env.ghs eff in
  let eff = eff_reset_overwritten eff in
  let p = rebase_pre env preold old dsp.ds_pre in
  let q = create_post ity dsp.ds_post in
  let xq = create_xpost dsp.ds_xpost in
  create_cty_defensive ~mask bl p q xq (get_oldies old) eff ity

(** Expressions *)

let check_used_pv e pv =
  if not (Sattr.mem Dterm.attr_w_unused_var_no pv.pv_vs.vs_name.id_attrs) &&
      Debug.test_noflag Dterm.debug_ignore_unused_var then
    begin
      let s = pv.pv_vs.vs_name.id_string in
      if (s = "" || s.[0] <> '_') && not (Spv.mem pv e.e_effect.eff_reads) then
        Warning.emit ?loc:pv.pv_vs.vs_name.id_loc "unused variable %s" s
    end

let e_let_check e ld = match ld with
  | LDvar (v,_) -> check_used_pv e v; e_let ld e
  | _           -> e_let ld e

let rec strip uloc attrs de = match de.de_node with
  | DEcast (de,_) -> strip uloc attrs de
  | DEuloc (de,loc) -> strip (Some (Some loc)) attrs de
  | DEattr (de,s) -> strip uloc (Sattr.union attrs s) de
  | _ -> uloc, attrs, de

let get_pv env n = Mstr.find_exn (Dterm.UnboundVar n) n env.pvm
let get_rs env n = Mstr.find_exn (Dterm.UnboundVar n) n env.rsm

let get_xs env = function
  | DElexn (n,_) -> Mstr.find_exn (UnboundExn n) n env.xsm
  | DEgexn xs -> xs

let proxy_attrs = Sattr.singleton proxy_attr

type header =
  | LS of let_defn
  | LX of xsymbol
  | LL of (let_defn * pvsymbol) Hpv.t

let put_header e = function
  | LS ld -> e_let_check e ld
  | LX xs -> e_exn xs e
  | LL ol -> Hpv.fold (fun _ (ld,_) e -> e_let ld e) ol e

type let_prefix =
  | LD of header
  | DA of env * dexpr

type let_postfix =
  | HD of header
  | EA of bool * expr

let vl_of_mask id mask ity =
  let mk_res m t = create_pvsymbol id ~ghost:(mask_ghost m) t in
  if ity_equal ity ity_unit then [] else
  match mask, ity.ity_node with
  | MaskTuple ml, Ityapp (_,tl,_) -> List.map2 mk_res ml tl
  | _ -> [mk_res mask ity]

let t_of_vl = function
  | [] -> t_void | [v] -> t_var v.pv_vs
  | vl -> t_tuple (List.map (fun v -> t_var v.pv_vs) vl)

let e_of_vl = function
  | [] -> e_void | [v] -> e_var v
  | vl -> e_tuple (List.map e_var vl)

let rec expr uloc env ({de_loc = loc} as de) =
  let uloc, attrs, de = strip uloc Sattr.empty de in
  let env = {env with lgh = false; cgh = false} in
  let e = Loc.try3 ?loc try_expr uloc env de in
  let loc = Opt.get_def loc uloc in
  if loc = None && Sattr.is_empty attrs
  then e else e_attr_push ?loc attrs e

and cexp uloc env ({de_loc = loc} as de) lpl =
  let uloc, attrs, de = strip uloc Sattr.empty de in
  if not (Sattr.is_empty attrs) then Warning.emit ?loc
    "Ignoring attributes over a higher-order expression";
  Loc.try4 ?loc try_cexp uloc env de lpl

and try_cexp uloc env ({de_dvty = argl,res} as de0) lpl =
  let rec drop vl al = match vl, al with
    | _::vl, _::al -> drop vl al | _ -> al in
  let rec eval_args tpl ghost plp al lpl = match al, lpl with
    | gh::al, DA (env, de) :: lpl ->
        let env = {env with ugh = env.ugh || ghost || gh} in
        let e = e_ghostify env.cgh (expr uloc env de) in
        let gha = not tpl && not gh && mask_ghost e.e_mask in
        eval_args tpl (ghost || gha) (EA (gh, e) :: plp) al lpl
    | al, LD hd :: lpl ->
        eval_args tpl ghost (HD hd :: plp) al lpl
    | [], _::_ -> assert false (* ill-typed *)
    | _, [] -> ghost, plp in
  let rec proxy_args ghost ldl vl = function
    | EA (_, ({e_node = Evar v} as e)) :: plp
      when Sattr.is_empty e.e_attrs ->
        proxy_args ghost ldl (v::vl) plp
    | EA (gh, e) :: plp ->
        let id = id_fresh ?loc:e.e_loc ~attrs:proxy_attrs "o" in
        let ld, v = let_var ~ghost:(ghost || gh) id e in
        proxy_args ghost (LS ld :: ldl) (v::vl) plp
    | HD hd :: plp ->
        proxy_args ghost (hd :: ldl) vl plp
    | [] -> ldl, vl in
  let apply app tpl gh s al lpl =
    let gh, plp = eval_args tpl gh [] al lpl in
    let ldl, vl = proxy_args gh [] [] plp in
    let argl = List.map ity_of_dity (drop vl argl) in
    env.cgh, ldl, app s vl argl (ity_of_dity res) in
  let c_app s lpl =
    let al = List.map (fun v -> v.pv_ghost) s.rs_cty.cty_args in
    let rec full_app al lpl = match al, lpl with
      | _::al, DA _::lpl -> full_app al lpl
      | al, LD _::lpl -> full_app al lpl
      | [], [] -> true | _ -> false in
    let tpl = is_rs_tuple s && full_app al lpl in
    apply c_app tpl (env.ghs || env.lgh || rs_ghost s) s al lpl in
  let c_pur ugh s lpl =
    let loc = Opt.get_def de0.de_loc uloc in
    if not (ugh || env.ghs || env.lgh || env.ugh) then Loc.errorm ?loc
      "Logical symbol %a is used in a non-ghost context" Pretty.print_ls s;
    apply c_pur false true s (List.map Util.ttrue s.ls_args) lpl in
  let c_oop s lpl =
    let rs = Srs.choose s in
    let loc = Opt.get_def de0.de_loc uloc in
    let app s vl al res =
      let nomatch s =
        let ty = match vl, al with
          | v::_, _ -> v.pv_vs.vs_ty
          | _, a::_ -> ty_of_ity a
          | _ -> assert false in
        (* this check can be cheated upon if the user names his type
           variables "'xi", but since we only do it for a better error
           message, we do not care all that much *)
        let tvm = ty_v_fold (fun m ({tv_name = id} as v) ->
          if id.id_string = "xi" then m else (* freeze v *)
          let ts = create_tysymbol (id_clone id) [] NoDef in
          Mtv.add v (ty_app ts []) m) Mtv.empty ty in
        let occur_check v ty = not (ty_v_any (tv_equal v) ty) in
        let rec unify m ty1 ty2 = match ty1.ty_node, ty2.ty_node with
          | Tyvar v1, Tyvar v2 when tv_equal v1 v2 -> m
          | Tyvar v1, _ when Mtv.mem v1 m -> unify m (Mtv.find v1 m) ty2
          | _, Tyvar v2 when Mtv.mem v2 m -> unify m ty1 (Mtv.find v2 m)
          | Tyvar v1, _ when occur_check v1 ty2 -> Mtv.add v1 ty2 m
          | _, Tyvar v2 when occur_check v2 ty1 -> Mtv.add v2 ty1 m
          | Tyapp (s1, tl1), Tyapp (s2, tl2) when ts_equal s1 s2 ->
              List.fold_left2 unify m tl1 tl2
          | _ -> raise Exit in
        let nomatch rs =
          let ity = (List.hd rs.rs_cty.cty_args).pv_ity in
          try ignore (unify tvm ty (ty_of_ity ity)); false
          with Exit -> true in
        Srs.for_all nomatch s in
      let app s cl = try Expr.c_app s vl al res :: cl with
        (* TODO: are there other valid exceptions here? *)
        | TypeMismatch _ -> cl in
      match Srs.fold app s [] with
      | [c] -> c
      | [] when nomatch s -> Loc.errorm ?loc
            "No suitable match found for notation %a" print_rs rs
      | _ -> Loc.errorm ?loc "Ambiguous notation: %a" print_rs rs in
    let al = List.map Util.ffalse rs.rs_cty.cty_args in
    apply app false (env.ghs || env.lgh) s al lpl in
  let proxy c =
    try
      let ld_of_lp = function LD ld -> ld | DA _ -> raise Exit in
      env.cgh, List.map ld_of_lp lpl, c
    with Exit ->
      let loc = Opt.get_def de0.de_loc uloc in
      let id = id_fresh ?loc ~attrs:proxy_attrs "h" in
      let ld, s = let_sym id ~ghost:(env.ghs || env.lgh) c in
      c_app s (LD (LS ld) :: lpl) in
  match de0.de_node with
  | DEvar (n,_,_) -> c_app (get_rs env n) lpl
  | DEsym (RS rs) -> c_app rs lpl
  | DEsym (OO ss) -> c_oop ss lpl
  | DEls_pure (ls,ugh) -> c_pur ugh ls lpl
  | DEapp (de1,de2) ->
      cexp uloc env de1 (DA (env, de2) :: lpl)
  | DEghost de ->
      (* if we were not in the ghost context until now, then
         we must ghostify the let-definitions down from here *)
      let cgh = env.cgh || not env.ghs in
      cexp uloc {env with ghs = true; cgh} de lpl
  | DEfun (bl,_,msk,dsp,de) ->
      let dvl _ _ _ = [] in
      let env = {env with ghs = env.ghs || env.lgh} in
      let bl = binders env.ghs bl in
      let c, dsp, _ = lambda uloc env bl msk dsp dvl de in
      check_fun env.inr None dsp c;
      proxy c
  | DEany (bl,dity,msk,dsp) ->
      let env = {env with ghs = env.ghs || env.lgh} in
      proxy (c_any (cty_of_spec env bl msk dsp dity))
  | DElet ((_,_,_,{de_dvty = ([],_)}) as dldf,de) ->
      let ld, env = var_defn uloc env dldf in
      cexp uloc env de (LD (LS ld) :: lpl)
  | DElet (dldf,de) ->
      let ldl0, env = sym_defn uloc env dldf in
      let lpl0 = List.rev_map (fun ld -> LD ld) ldl0 in
      cexp uloc env de (List.rev_append lpl0 lpl)
  | DErec (drdf,de) ->
      let ld, env = rec_defn uloc env drdf in
      cexp uloc env de (LD (LS ld) :: lpl)
  | DEexn (id,dity,mask,de) ->
      let mask = if env.ghs then MaskGhost else mask in
      let xs = create_xsymbol id ~mask (ity_of_dity dity) in
      cexp uloc (add_xsymbol env xs) de (LD (LX xs) :: lpl)
  | DElabel (id,de) ->
      let env, old = add_label env id.pre_name in
      cexp uloc env de (LD (LL old) :: lpl)
  | DEvar_pure _ | DEpv_pure _ | DEoptexn _
  | DEsym _ | DEconst _ | DEnot _ | DEand _ | DEor _ | DEif _
  | DEmatch _ | DEassign _ | DEwhile _ | DEfor _ | DEraise _ | DEassert _
  | DEpure _ | DEabsurd | DEtrue | DEfalse -> assert false (* expr-only *)
  | DEcast _ | DEuloc _ | DEattr _ -> assert false (* already stripped *)

and try_expr uloc env ({de_dvty = argl,res} as de0) =
  match de0.de_node with
  | DEvar (n,_,_) when argl = [] ->
      e_var (get_pv env n)
  | DEvar_pure (n,_,_) ->
      e_pure (t_var (get_pv env n).pv_vs)
  | DEsym (PV v) ->
      e_var v
  | DEpv_pure v ->
      e_pure (t_var v.pv_vs)
  | DEconst (c,dity) ->
      e_const c (ity_of_dity dity)
  | DEapp ({de_dvty = ([],_)} as de1, de2) ->
      let e1 = expr uloc env de1 in
      let ugh = env.ugh || e1.e_mask = MaskGhost in
      let e2 = expr uloc {env with ugh} de2 in
      e_app rs_func_app [e1; e2] [] (ity_of_dity res)
  | DEvar _ | DEsym _ | DEls_pure _ | DEapp _ | DEfun _ | DEany _ ->
      let cgh,ldl,c = try_cexp uloc env de0 [] in
      let e = e_ghostify cgh (e_exec c) in
      List.fold_left put_header e ldl
  | DElet ((_,_,_,{de_dvty = ([],_)}) as dldf,de) ->
      let ld, env = var_defn uloc env dldf in
      let e2 = expr uloc env de in
      e_let_check e2 ld
  | DElet (dldf,de) ->
      let ldl, env = sym_defn uloc env dldf in
      List.fold_left put_header (expr uloc env de) ldl
  | DErec (drdf,de) ->
      let ld, env = rec_defn uloc env drdf in
      e_let_check (expr uloc env de) ld
  | DEnot de ->
      e_not (expr uloc env de)
  | DEand (de1,de2) ->
      e_and (expr uloc env de1) (expr uloc env de2)
  | DEor (de1,de2) ->
      e_or (expr uloc env de1) (expr uloc env de2)
  | DEif (de1,de2,de3) ->
      e_if (expr uloc env de1) (expr uloc env de2) (expr uloc env de3)
  | DEassign al ->
      let conv (de1,f,de2) =
        let e1 = expr uloc {env with ugh = false} de1 in
        let ugh = rs_ghost f || e1.e_mask = MaskGhost in
        e1, f, expr uloc {env with ugh} de2 in
      e_assign (List.map conv al)
  | DEwhile (de1,dinv,dvarl,de2) ->
      let env = {env with ugh = false} in
      let e1 = expr uloc env de1 in
      let e2 = expr uloc env de2 in
      let inv = get_later env dinv in
      let varl = get_later env dvarl in
      e_while e1 (create_invariant inv) varl e2
  | DEfor (id,de_from,dir,de_to,dinv,de) ->
      let env = {env with ugh = false} in
      let e_from = expr uloc env de_from in
      let e_to = expr uloc env de_to in
      let v = create_pvsymbol id e_from.e_ity in
      let env = add_pvsymbol env v in
      let i = if ity_equal v.pv_ity ity_int then v else
        create_pvsymbol id ~ghost:true ity_int in
      let env = if pv_equal i v then env else
        { env with idx = Mpv.add v i env.idx } in
      let e = expr uloc env de in
      let inv = get_later env dinv in
      e_for v e_from dir e_to i (create_invariant inv) e
  | DEmatch (de1,bl,xl) ->
      let e1 = expr uloc env de1 in
      (* regular branches *)
      let mask = if env.ghs then MaskGhost else e1.e_mask in
      let mk_branch (dp,de) =
        let vm, pat = create_prog_pattern dp.dp_pat e1.e_ity mask in
        let e = expr uloc (add_pv_map env vm) de in
        Mstr.iter (fun _ v -> check_used_pv e v) vm;
        pat, e in
      let bl = List.rev_map mk_branch bl in
      (* TODO: this is the right place to show the missing patterns,
         but we do not have access to the current known_map to do that *)
      let exhaustive = bl = [] ||
        let v = create_vsymbol (id_fresh "x") (ty_of_ity e1.e_ity) in
        let pl = List.rev_map (fun (p,_) -> [p.pp_pat]) bl in
        Pattern.is_exhaustive [t_var v] pl in
      let bl = if exhaustive then bl else begin
        if List.length bl > 1 then Warning.emit ?loc:de0.de_loc
          "Non-exhaustive pattern matching, asserting `absurd'";
        let _,pp = create_prog_pattern PPwild e1.e_ity mask in
        (pp, e_absurd (ity_of_dity res)) :: bl end in
      (* exception branches *)
      let add_branch m (xs,dp,de) =
        let xs = get_xs env xs in
        let mask = if env.ghs then MaskGhost else xs.xs_mask in
        let vm, pat = create_prog_pattern dp.dp_pat xs.xs_ity mask in
        let e = expr uloc (add_pv_map env vm) de in
        Mstr.iter (fun _ v -> check_used_pv e v) vm;
        Mxs.add xs ((pat, e) :: Mxs.find_def [] xs m) m in
      let xsm = List.fold_left add_branch Mxs.empty xl in
      let is_simple p = match p.pat_node with
        | Papp (fs,[]) -> is_fs_tuple fs
        | Pvar _ | Pwild -> true | _ -> false in
      let conv_simple p (ity,ghost) = match p.pat_node with
        | Pvar v -> Ity.restore_pv v
        | _ -> create_pvsymbol (id_fresh "_") ~ghost ity in
      let mk_branch xs = function
        | [{ pp_pat = { pat_node = Pvar v }}, e] ->
            [Ity.restore_pv v], e
        | [{ pp_pat = { pat_node = (Pwild | Papp (_,[])) }}, e]
          when ity_equal xs.xs_ity ity_unit ->
            [], e
        | [{ pp_pat = { pat_node = Pwild }}, e] ->
            let ghost = env.ghs || mask_ghost xs.xs_mask in
            [create_pvsymbol (id_fresh "_") ~ghost xs.xs_ity], e
        | [{ pp_pat = { pat_node = Papp (fs,(_::_::_ as pl)) }}, e]
          when is_fs_tuple fs && List.for_all is_simple pl ->
            let mask = if env.ghs then MaskGhost else xs.xs_mask in
            let tyl = match xs.xs_ity.ity_node with (* tuple *)
              | Ityapp (_,tyl,_) -> tyl | _ -> assert false in
            let ghl = match mask with
              | MaskTuple ml -> List.map mask_ghost ml
              | MaskVisible -> List.map Util.ffalse pl
              | MaskGhost -> List.map Util.ttrue pl in
            List.map2 conv_simple pl (List.combine tyl ghl), e
        | bl ->
            let mask = if env.ghs then MaskGhost else xs.xs_mask in
            let vl = vl_of_mask (id_fresh "q") mask xs.xs_ity in
            let t = t_of_vl vl and e = e_of_vl vl in
            let pl = List.rev_map (fun (p,_) -> [p.pp_pat]) bl in
            let bl = if Pattern.is_exhaustive [t] pl then bl else
              let _,pp = create_prog_pattern PPwild xs.xs_ity mask in
              (pp, e_raise xs e (ity_of_dity res)) :: bl in
            vl, e_match e (List.rev bl) Mxs.empty in
      e_match e1 (List.rev bl) (Mxs.mapi mk_branch xsm)
  | DEraise (xs,de) ->
      let {xs_mask = mask} as xs = get_xs env xs in
      let env = {env with ugh = mask = MaskGhost} in
      e_raise xs (expr uloc env de) (ity_of_dity res)
  | DEghost de ->
      e_ghostify true (expr uloc {env with ghs = true} de)
  | DEassert (ak,f) ->
      e_assert ak (create_assert (get_later env f))
  | DEpure (t, _) ->
      e_pure (get_later env t)
  | DEabsurd ->
      e_absurd (ity_of_dity res)
  | DEtrue ->
      e_true
  | DEfalse ->
      e_false
  | DEexn (id,dity,mask,de) ->
      let mask = if env.ghs then MaskGhost else mask in
      let xs = create_xsymbol id ~mask (ity_of_dity dity) in
      e_exn xs (expr uloc (add_xsymbol env xs) de)
  | DEoptexn (id,dity,mask,de) ->
      let mask = if env.ghs then MaskGhost else mask in
      let xs = create_xsymbol id ~mask (ity_of_dity dity) in
      let e = expr uloc (add_xsymbol env xs) de in
      if not (Sxs.mem xs e.e_effect.eff_raises) then e else
      let vl = vl_of_mask (id_fresh "r") mask xs.xs_ity in
      let branches = Mxs.singleton xs (vl, e_of_vl vl) in
      e_exn xs (e_match e [] branches)
  | DElabel (id,de) ->
      let env, old = add_label env id.pre_name in
      let put _ (ld,_) e = e_let ld e in
      Hpv.fold put old (expr uloc env de)
  | DEcast _ | DEuloc _ | DEattr _ ->
      assert false (* already stripped *)

and var_defn uloc env (id,gh,kind,de) =
  let e = match kind with
    | RKlemma -> Loc.errorm ?loc:id.pre_loc
        "lemma-functions must have parameters"
    | RKlocal -> Loc.errorm ?loc:id.pre_loc
        "illegal kind qualifier"
    | RKfunc | RKpred | RKnone ->
        let e = expr uloc {env with ugh = gh} de in
        e_ghostify env.cgh e in
  let ld, v = let_var id ~ghost:(gh || env.ghs) e in
  ld, add_pvsymbol env v

and sym_defn uloc env (id,gh,kind,de) =
  let lgh = env.ghs || gh || kind = RKlemma in
  let cgh, ldl, c = cexp uloc {env with lgh; ugh = false} de [] in
  let ld, s = let_sym id ~ghost:(lgh || cgh) ~kind c in
  LS ld :: ldl, add_rsymbol env s

and rec_defn uloc ({inr = inr} as env0) {fds = dfdl} =
  let step1 env (id, gh, kind, bl, res, mask, dsp, dvl, de) =
    let ghost = env.ghs || gh || kind = RKlemma in
    let pvl = binders ghost bl in
    let ity = Loc.try1 ?loc:de.de_loc ity_of_dity res in
    let cty = create_cty ~mask pvl [] [] Mxs.empty Mpv.empty eff_empty ity in
    let rs = create_rsymbol id ~ghost ~kind:RKnone cty in
    add_rsymbol env rs, (rs, kind, mask, dsp, dvl, de) in
  let env = {env0 with inr = true; ugh = false} in
  let env, fdl = Lists.map_fold_left step1 env dfdl in
  let step2 (rs, kind, mask, dsp, dvl, de) (fdl,dspl) =
    let env = {env with ghs = env.ghs || rs_ghost rs} in
    let {rs_name = {id_string = nm; id_loc = loc}; rs_cty = c} = rs in
    let lam, dsp, dvl = lambda uloc env c.cty_args mask dsp dvl de in
    if c_ghost lam && not (rs_ghost rs) then Loc.errorm ?loc
      "Function %s must be explicitly marked ghost" nm;
    if mask_spill lam.c_cty.cty_mask c.cty_mask then Loc.errorm ?loc
      "Function %s returns unexpected ghost results" nm;
    (rs, lam, dvl, kind)::fdl, dsp::dspl in
  (* check for unexpected aliases in case of trouble *)
  let fdl, dspl = try List.fold_right step2 fdl ([],[]) with
    | Loc.Located (_, Ity.TypeMismatch _) | Ity.TypeMismatch _ as exn ->
        List.iter (fun ({rs_name = {id_loc = loc}} as rs,_,_,_,_,_) ->
          Loc.try2 ?loc check_aliases true rs.rs_cty) fdl;
        raise exn in
  let ld, rdl = try let_rec fdl with
    | Loc.Located (_, Ity.TypeMismatch _) | Ity.TypeMismatch _ as exn ->
        List.iter (fun ({rs_name = {id_loc = loc}},lam,_,_) ->
          Loc.try2 ?loc check_aliases true lam.c_cty) fdl;
        raise exn in
  let add_fd env {rec_sym = s; rec_rsym = rs; rec_fun = c} dsp =
    Loc.try4 ?loc:rs.rs_name.id_loc check_fun inr (Some rs) dsp c;
    add_rsymbol env s in
  ld, List.fold_left2 add_fd env0 rdl dspl

and lambda uloc env pvl mask dsp dvl de =
  let ugh = env.ugh || mask = MaskGhost in
  let env = add_binders {env with ugh} pvl in
  let preold = Mstr.find_opt old_label env.old in
  let env, old = add_label env old_label in
  let e = expr uloc env de in
  let dsp = get_later env dsp e.e_ity in
  let dvl = get_later env dvl in
  let dvl = rebase_variant env preold old dvl in
  let p = rebase_pre env preold old dsp.ds_pre in
  let q = create_post e.e_ity dsp.ds_post in
  let xq = create_xpost dsp.ds_xpost in
  let e = if not dsp.ds_diverge then e
          else e_attr_add Vc.nt_attr e in
  c_fun ~mask pvl p q xq (get_oldies old) e, dsp, dvl

let rec_defn ?(keep_loc=true) drdf =
  let uloc = if keep_loc then None else Some None in
  fst (rec_defn uloc env_empty drdf)

let rec mask_of_fun de = match de.de_node with
  | DEfun (_,_,msk,_,_) -> msk
  | DEghost de | DEcast (de,_)
  | DEuloc (de,_) | DEattr (de,_) -> mask_of_fun de
  | _ -> MaskGhost (* a safe default for checking *)

let let_defn ?(keep_loc=true) (id, ghost, kind, de) =
  let uloc = if keep_loc then None else Some None in
  let {pre_name = nm; pre_loc = loc} = id in
  let ghost = ghost || kind = RKlemma in
  match kind, de.de_dvty with
  | _, (_::_, _) ->
      let env = {env_empty with lgh = ghost} in
      let cgh, ldl, c = cexp uloc env de [] in
      if ldl <> [] then Loc.errorm ?loc:de.de_loc
        "Illegal top-level function definition";
      if (cgh || c_ghost c) && not ghost then Loc.errorm ?loc
        "Function %s must be explicitly marked ghost" nm;
      let spl = mask_spill c.c_cty.cty_mask (mask_of_fun de) in
      if spl && not ghost then Loc.errorm ?loc
        "Function %s returns unexpected ghost results" nm;
      fst (let_sym id ~ghost ~kind c)
  | (RKfunc | RKpred), ([], _) ->
      let e = expr uloc {env_empty with ugh = ghost} de in
      if mask_ghost e.e_mask && not ghost then Loc.errorm ?loc
        "Function %s must be explicitly marked ghost" nm;
      if not e.e_ity.ity_pure then Loc.errorm ?loc
        "This value is mutable, it cannot be used as pure";
      let c = c_fun [] [] [] Mxs.empty Mpv.empty e in
      (* the rsymbol will carry a single postcondition "the result
         is equal to the logical constant". Any user-written spec
         will be checked once, in-place, under Eexec. Since kind
         guarantees the absence of effects and any external reads,
         this one-time check is sufficient, and we won't pollute
         the later WPs with the copies of the spec. When preparing
         the logical constant definition, we must extract that
         user-written specification from under Cfun, and put it
         into an axiom. *)
      fst (let_sym id ~ghost ~kind c)
  | RKnone, ([], _) ->
      let e = expr uloc {env_empty with ugh = ghost} de in
      if mask_ghost e.e_mask && not ghost then Loc.errorm ?loc
        "Variable %s must be explicitly marked ghost" nm;
      fst (let_var id ~ghost e)
  | RKlemma, ([], _) -> Loc.errorm ?loc
      "Lemma-functions must have parameters"
  | RKlocal, _ -> invalid_arg "Dexpr.let_defn"

let expr ?(keep_loc=true) ?(ughost=false) de =
  let uloc = if keep_loc then None else Some None in
  expr uloc {env_empty with ugh = ughost} de

let () = Exn_printer.register (fun fmt e -> match e with
  | UnboundLabel s ->
      Format.fprintf fmt "unbound label %s" s
  | UnboundExn s ->
      Format.fprintf fmt "unbound exception %s" s
  | _ -> raise e)
