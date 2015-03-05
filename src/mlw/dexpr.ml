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
open Ty
open Term
open Ity
open Expr

(** Program types *)

type dity =
  | Dutv of tvsymbol          (* undestructible "user" type variable *)
  | Dvar of dvar ref          (* destructible "fresh" type variable *)
  | Durg of ity * dity        (* undestructible "user" region, for global refs *)
  | Dreg of dvar ref * dity   (* destructible "fresh" region *)
  | Dapp of itysymbol * dity list * dity list
  | Dpur of itysymbol * dity list

and dvar =
  | Dtvs of tvsymbol          (* unassigned fresh type variable *)
  | Dval of dity              (* destructive binding *)

(* In Dapp, the second dity list only contains Dreg's and Durg's.
   In Dreg and Durg, the dity field is a Dapp of the region's type.
   In Dreg, the dvar field leads to another Dreg or Durg.
   In Durg, the ity field is an Ityreg. *)

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)

let dity_of_dvty (argl,res) =
  List.fold_right (fun a d -> Dpur (its_func, [a;d])) argl res

let dvar_fresh n = ref (Dtvs (create_tvsymbol (id_fresh n)))

let dreg_fresh dity = Dreg (dvar_fresh "rho", dity)

let dity_of_ity ity =
  let hr = Hreg.create 3 in
  let rec dity ity = match ity.ity_node with
    | Ityapp (s,tl,rl) -> Dapp (s, List.map dity tl, List.map dreg rl)
    | Itypur (s,tl)    -> Dpur (s, List.map dity tl)
    | Ityvar v -> Dutv v
    | Ityreg r -> dreg r
  and dreg reg =
    try Hreg.find hr reg with Not_found ->
    let {reg_its = s; reg_args = tl; reg_regs = rl} = reg in
    let d = Dapp (s, List.map dity tl, List.map dreg rl) in
    let r = dreg_fresh d in Hreg.add hr reg r; r in
  dity ity

let reg_of_ity = function
  | {ity_node = Ityreg reg} -> reg
  | _ -> assert false

let rec ity_of_dity = function
  | Dvar ({contents = Dval d})
  | Dreg ({contents = Dval d}, _) ->
      ity_of_dity d
  | Dvar r ->
      let v = create_tvsymbol (id_fresh "xi") in
      r := Dval (Dutv v); ity_var v
  | Dreg (r, d) ->
      let ity = ity_of_dity d in
      r := Dval (Durg (ity, d)); ity
  | Dutv v -> ity_var v
  | Durg (ity,_) -> ity
  | Dapp (s,tl,rl) ->
      let reg_of_dity r = reg_of_ity (ity_of_dity r) in
      ity_app s (List.map ity_of_dity tl) (List.map reg_of_dity rl)
  | Dpur (s,tl) ->
      ity_pur s (List.map ity_of_dity tl)

(** Destructive type unification *)

let rec occur_check v = function
  | Dvar {contents = Dval d} | Dreg (_,d) | Durg (_,d) -> occur_check v d
  | Dvar {contents = Dtvs u} | Dutv u -> if tv_equal u v then raise Exit
  | Dapp (_,dl,_) | Dpur (_,dl) -> List.iter (occur_check v) dl

let rec dity_unify d1 d2 = match d1,d2 with
  | Dvar {contents = Dval d1}, d2
  | d1, Dvar {contents = Dval d2}
  | Durg (_,d1), Durg (_,d2) | Durg (_,d1), Dreg (_,d2)
  | Dreg (_,d1), Durg (_,d2) | Dreg (_,d1), Dreg (_,d2) ->
      dity_unify d1 d2
  | Dvar {contents = Dtvs u},
    Dvar {contents = Dtvs v} when tv_equal u v ->
      ()
  | Dvar ({contents = Dtvs v} as r), d
  | d, Dvar ({contents = Dtvs v} as r) ->
      occur_check v d;
      r := Dval d
  | Dutv u, Dutv v when tv_equal u v ->
      ()
  |(Dapp (s1,dl1,_), Dapp (s2,dl2,_)
  | Dpur (s1,dl1),   Dpur (s2,dl2)) when its_equal s1 s2 ->
      List.iter2 dity_unify dl1 dl2
  | _ -> raise Exit

(** Reunify regions *)

let dtvs_queue : dvar ref Queue.t = Queue.create ()

let unify_queue : (dity * dity) Queue.t = Queue.create ()

let dity_fresh () =
  let r = dvar_fresh "mu" in
  Queue.add r dtvs_queue;
  Dvar r

let rec dity_refresh ht = function
  | Dreg ({contents = Dtvs v},d) ->
      begin try Htv.find ht v with Not_found ->
      let r = dreg_fresh (dity_refresh ht d) in
      Htv.add ht v r; r end
  | Dreg _ -> assert false
  | Dpur (s,dl) ->    Dpur (s, List.map (dity_refresh ht) dl)
  | Dapp (s,dl,rl) -> Dapp (s, List.map (dity_refresh ht) dl,
                               List.map (dity_refresh ht) rl)
  | Dvar {contents = Dval d} -> dity_refresh (Htv.create 3) d
  |(Dvar {contents = Dtvs _} | Dutv _ | Durg _) as d -> d

let dity_refresh d = dity_refresh (Htv.create 3) d

let dity_unify_weak = dity_unify

let dity_unify d1 d2 = dity_unify d1 d2; Queue.add (d1,d2) unify_queue

let rec reunify d1 d2 = match d1,d2 with
  | Dvar {contents = Dval d1}, d2
  | d1, Dvar {contents = Dval d2}
  | Dreg ({contents = Dval d1},_), d2
  | d1, Dreg ({contents = Dval d2},_) ->
      reunify d1 d2
  | Dvar _, Dvar _ | Dutv _, Dutv _ | Durg _, Durg _ ->
      ()
  | Dreg ({contents = Dtvs u},_),
    Dreg ({contents = Dtvs v},_) when tv_equal u v ->
      ()
  | Dreg (r, d1), (Dreg (_, d2) as d)
  | Dreg (r, d1), (Durg (_, d2) as d)
  | (Durg (_, d1) as d), Dreg (r, d2) ->
      reunify d1 d2;
      r := Dval d
  | Dapp (_,dl1,rl1), Dapp (_,dl2,rl2) ->
      List.iter2 reunify dl1 dl2;
      List.iter2 reunify rl1 rl2
  | Dpur (_,dl1), Dpur (_,dl2) ->
      List.iter2 reunify dl1 dl2
  | _ -> assert false

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
  | Dpur (s,_) -> its_equal s its_bool
  | _ -> false

let dvty_is_chainable = function
  | [t1;t2],t ->
      dity_is_bool t && not (dity_is_bool t1) && not (dity_is_bool t2)
  | _ -> false

(** Built-in types *)

let dity_int  = Dpur (its_int,  [])
let dity_real = Dpur (its_real, [])
let dity_bool = Dpur (its_bool, [])
let dity_unit = Dpur (its_unit, [])

let dvty_int  = [], dity_int
let dvty_real = [], dity_real
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

let rec print_dity pri fmt = function
  | Dvar {contents = Dval d}
  | Dreg ({contents = Dval d},_) ->
      print_dity pri fmt d
  | Dvar {contents = Dtvs v}
  | Dutv v ->
      Pretty.print_tv fmt v
  | Dreg ({contents = Dtvs v},d) ->
      Format.fprintf fmt (protect_on (pri > 1) "%a@ @@%s")
        (print_dity 0) d (Ident.id_unique rprinter v.tv_name)
  | Durg (ity,d) ->
      Format.fprintf fmt (protect_on (pri > 1) "%a@ @@%s")
        (print_dity 0) d (Ident.id_unique rprinter (reg_of_ity ity).reg_name)
  | Dpur (s,[t1;t2]) when its_equal s its_func ->
      Format.fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_dity 1) t1 (print_dity 0) t2
  | Dpur (s,tl) when is_ts_tuple s.its_ts ->
      Format.fprintf fmt "(%a)" (Pp.print_list Pp.comma (print_dity 0)) tl
  | Dpur (s,tl) when s.its_mutable || s.its_regions <> [] ->
      Format.fprintf fmt (protect_on (pri > 1 && tl <> []) "{%a}%a")
        Pretty.print_ts s.its_ts (print_args (print_dity 2)) tl
  | Dpur (s,tl) ->
      Format.fprintf fmt (protect_on (pri > 1 && tl <> []) "%a%a")
        Pretty.print_ts s.its_ts (print_args (print_dity 2)) tl
  | Dapp (s,tl,rl) ->
      Format.fprintf fmt (protect_on (pri > 1) "%a%a%a")
        Pretty.print_ts s.its_ts (print_args (print_dity 2)) tl
          (print_regs (print_dity 0)) rl

let print_dity fmt d = print_dity 0 fmt d

(* Specialization of symbols *)

let specialize_scheme tvs (argl,res) =
  let hv = Htv.create 3 and hr = Htv.create 3 in
  let rec spec_dity = function
    | Durg _ as d -> d
    | Dvar {contents = Dval d} | Dreg ({contents = Dval d},_) -> spec_dity d
    | Dvar {contents = Dtvs v} | Dutv v as d -> get_tv v d
    | Dreg ({contents = Dtvs v},d) -> get_reg v d
    | Dapp (s,dl,rl) -> Dapp (s, List.map spec_dity dl, List.map spec_dity rl)
    | Dpur (s,dl)    -> Dpur (s, List.map spec_dity dl)
  and get_tv v d = try Htv.find hv v with Not_found ->
    let nd = dity_fresh () in
    (* can't return d, might differ in regions *)
    if not (Stv.mem v tvs) then dity_unify_weak nd d;
    Htv.add hv v nd; nd
  and get_reg v d = try Htv.find hr v with Not_found ->
    let r = dreg_fresh (spec_dity d) in
    Htv.add hr v r; r in
  List.map spec_dity argl, spec_dity res

let spec_ity hv hr frz ity =
  let rec dity ity = match ity.ity_node with
    | Ityreg r -> dreg r
    | Ityvar v -> if Mtv.mem v frz.isb_tv then Dutv v else get_tv v
    | Ityapp (s,tl,rl) -> Dapp (s, List.map dity tl, List.map dreg rl)
    | Itypur (s,tl)    -> Dpur (s, List.map dity tl)
  and get_tv v = try Htv.find hv v with Not_found ->
    let nd = dity_fresh () in Htv.add hv v nd; nd
  and dreg reg = try Hreg.find hr reg with Not_found ->
    let {reg_its = s; reg_args = tl; reg_regs = rl} = reg in
    let d = Dapp (s, List.map dity tl, List.map dreg rl) in
    let r = if Mreg.mem reg frz.isb_reg then
      Durg (ity_reg reg, d) else dreg_fresh d in
    Hreg.add hr reg r; r in
  dity ity

let specialize_pv {pv_ity = ity} =
  spec_ity (Htv.create 3) (Hreg.create 3) (ity_freeze isb_empty ity) ity

let specialize_xs {xs_ity = ity} =
  spec_ity (Htv.create 3) (Hreg.create 3) (ity_freeze isb_empty ity) ity

let specialize_rs {rs_cty = cty} =
  let hv = Htv.create 3 and hr = Hreg.create 3 in
  let spec ity = spec_ity hv hr cty.cty_freeze ity in
  List.map (fun v -> spec v.pv_ity) cty.cty_args, spec cty.cty_result

(** Patterns *)

type dpattern = {
  dp_pat  : pre_pattern;
  dp_dity : dity;
  dp_vars : dity Mstr.t;
  dp_loc  : Loc.position option;
}

type dpattern_node =
  | DPwild
  | DPvar  of preid
  | DPapp  of rsymbol * dpattern list
  | DPor   of dpattern * dpattern
  | DPas   of dpattern * preid
  | DPcast of dpattern * ity

(** Specifications *)

type ghost = bool

type dbinder = preid option * ghost * dity

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
  ds_diverge : bool;
  ds_checkrw : bool;
}

type dspec = ty -> dspec_final
  (* Computation specification is also parametrized by the result type.
     All vsymbols in the postcondition clauses in the [ds_post] field
     must have this type. All vsymbols in the exceptional postcondition
     clauses must have the type of the corresponding exception. *)

(** Expressions *)

type dinvariant = term list

type dexpr = {
  de_node : dexpr_node;
  de_dvty : dvty;
  de_loc  : Loc.position option;
}

and dexpr_node =
  | DEvar of string * dvty
  | DEpv of pvsymbol
  | DErs of rsymbol
  | DEconst of Number.constant
  | DEapp of dexpr * dexpr
  | DEfun of dbinder list * dspec later * dexpr
  | DEany of dbinder list * dspec later * dity
  | DElet of dlet_defn * dexpr
  | DErec of drec_defn * dexpr
  | DEnot of dexpr
  | DElazy of lazy_op * dexpr * dexpr
  | DEif of dexpr * dexpr * dexpr
  | DEcase of dexpr * (dpattern * dexpr) list
  | DEassign of (dexpr * rsymbol * dexpr) list
  | DEwhile of dexpr * dinvariant later * variant list later * dexpr
  | DEfor of preid * dexpr * for_direction * dexpr * dinvariant later * dexpr
  | DEtry of dexpr * (xsymbol * dpattern * dexpr) list
  | DEraise of xsymbol * dexpr
  | DEghost of dexpr
  | DEassert of assertion_kind * term later
  | DEpure of term later
  | DEabsurd
  | DEtrue
  | DEfalse
  | DEmark of preid * dexpr
  | DEcast of dexpr * ity
  | DEuloc of dexpr * Loc.position
  | DElabel of dexpr * Slab.t

and dlet_defn = preid * ghost * rs_kind * dexpr

and drec_defn = { fds : dfun_defn list }

and dfun_defn = preid * ghost * rs_kind *
  dbinder list * dspec later * variant list later * dexpr

type dval_decl = preid * ghost * rs_kind *
  dbinder list * dspec later * dity

(** Environment *)

type denv = {
  frozen : dity list;
  locals : (Stv.t option * dvty) Mstr.t;
}

let denv_empty = { frozen = []; locals = Mstr.empty }

let is_frozen frozen v =
  try List.iter (occur_check v) frozen; false with Exit -> true

let freeze_dvty frozen (argl,res) =
  let rec add l = function
    | Dreg (_,d) | Durg (_,d)
    | Dvar { contents = Dval d } -> add l d
    | Dvar { contents = Dtvs _ } as d -> d :: l
    | Dutv _ as d -> d :: l
    | Dapp (_,tl,_) | Dpur (_,tl) -> List.fold_left add l tl in
  List.fold_left add (add frozen res) argl

let free_vars frozen (argl,res) =
  let rec add s = function
    | Dreg (_,d) | Durg (_,d)
    | Dvar { contents = Dval d } -> add s d
    | Dvar { contents = Dtvs v }
    | Dutv v -> if is_frozen frozen v then s else Stv.add v s
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
    | Dreg (_,d) | Durg (_,d)
    | Dvar { contents = Dval d } -> is_explicit d
    | Dvar { contents = Dtvs _ } -> false
    | Dutv _ -> true
    | Dapp (_,tl,_) | Dpur (_,tl) -> List.for_all is_explicit tl in
  if List.for_all is_explicit argl && is_explicit res
  then denv_add_rec_poly denv frozen0 id dvty
  else denv_add_rec_mono denv id dvty

let denv_add_var denv id dity = denv_add_mono denv id ([], dity)

let denv_add_let denv (id,_,_,({de_dvty = dvty} as de)) =
  if fst dvty = [] then denv_add_mono denv id dvty else
  let rec is_value de = match de.de_node with
    | DEghost de | DEuloc (de,_) | DElabel (de,_) -> is_value de
    | DEvar _ | DErs _ | DEfun _ | DEany _ -> true
    | _ -> false in
  if is_value de
  then denv_add_poly denv id dvty
  else denv_add_mono denv id dvty

let denv_add_args { frozen = frozen; locals = locals } bl =
  let l = List.fold_left (fun l (_,_,t) -> t::l) frozen bl in
  let add s (id,_,t) = match id with
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

(** Generation of letrec blocks *)

type pre_fun_defn = preid * ghost * rs_kind * dbinder list *
  dity * (denv -> dspec later * variant list later * dexpr)

exception DupId of preid

let drec_defn denv0 prel =
  if prel = [] then invalid_arg "Dexpr.drec_defn: empty function list";
  let add s (id,_,_,_,_,_) = Sstr.add_new (DupId id) id.pre_name s in
  let _ = try List.fold_left add Sstr.empty prel with DupId id ->
    Loc.errorm ?loc:id.pre_loc "duplicate function name %s" id.pre_name in
  let add denv (id,_,_,bl,res,_) =
    if bl = [] then invalid_arg "Dexpr.drec_defn: empty argument list";
    let argl = List.map (fun (_,_,t) -> t) bl in
    denv_add_rec denv denv0.frozen id (argl,res) in
  let denv1 = List.fold_left add denv0 prel in
  let parse (id,gh,pk,bl,res,pre) =
    let dsp, dvl, de = pre (denv_add_args denv1 bl) in
    dexpr_expected_type_weak de res;
    (id,gh,pk,bl,dsp,dvl,de) in
  let fdl = List.map parse prel in
  let add denv (id,_,_,bl,_,_,{de_dvty = dvty}) =
    (* just in case we linked some polymorphic type var to the outer context *)
    let check tv = if is_frozen denv0.frozen tv then Loc.errorm ?loc:id.pre_loc
      "This function is expected to be polymorphic in type variable %a"
      Pretty.print_tv tv in
    begin match Mstr.find_opt id.pre_name denv1.locals with
    | Some (Some tvs, _) -> Stv.iter check tvs
    | Some (None, _) | None -> assert false
    end;
    let argl = List.map (fun (_,_,t) -> t) bl in
    denv_add_poly denv id (argl, dity_of_dvty dvty) in
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
    | DEpv pv ->
        [], specialize_pv pv
    | DErs rs ->
        specialize_rs rs
    | DEconst (Number.ConstInt _) ->
        dvty_int
    | DEconst (Number.ConstReal _) ->
        dvty_real
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
    | DEfun (bl,_,de) ->
        List.map (fun (_,_,t) -> t) bl, dity_of_dvty de.de_dvty
    | DEany (bl,_,res) ->
        List.map (fun (_,_,t) -> t) bl, res
    | DElet (_,de)
    | DErec (_,de) ->
        de.de_dvty
    | DEnot de ->
        dexpr_expected_type de dity_bool;
        de.de_dvty
    | DElazy (_,de1,de2) ->
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 dity_bool;
        de1.de_dvty
    | DEif (de1,de2,de3) ->
        let res = dity_fresh () in
        dexpr_expected_type de1 dity_bool;
        dexpr_expected_type de2 res;
        dexpr_expected_type de3 res;
        [], res
    | DEcase (_,[]) ->
        invalid_arg "Dexpr.dexpr: empty branch list in DEcase"
    | DEcase (de,bl) ->
        let ety = dity_fresh () in
        let res = dity_fresh () in
        dexpr_expected_type de ety;
        List.iter (fun (dp,de) ->
          dpat_expected_type dp ety;
          dexpr_expected_type de res) bl;
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
        de2.de_dvty
    | DEfor (_,de_from,_,de_to,_,de) ->
        dexpr_expected_type de_from dity_int;
        dexpr_expected_type de_to dity_int;
        dexpr_expected_type de dity_unit;
        de.de_dvty
    | DEtry (_,[]) ->
        invalid_arg "Dexpr.dexpr: empty branch list in DEtry"
    | DEtry (de,bl) ->
        let res = dity_fresh () in
        dexpr_expected_type de res;
        List.iter (fun (xs,dp,de) ->
          dpat_expected_type dp (specialize_xs xs);
          dexpr_expected_type de res) bl;
        [], res
    | DEraise (xs,de) ->
        dexpr_expected_type de (specialize_xs xs);
        [], dity_fresh ()
    | DEghost de ->
        de.de_dvty
    | DEassert _ ->
        dvty_unit
    | DEpure _
    | DEabsurd ->
        [], dity_fresh ()
    | DEtrue
    | DEfalse ->
        dvty_bool
    | DEcast (de,ity) ->
        dexpr_expected_type_weak de (dity_of_ity ity);
        de.de_dvty
    | DEmark (_,de)
    | DEuloc (de,_)
    | DElabel (de,_) ->
        de.de_dvty in
  let dvty = Loc.try1 ?loc get_dvty node in
  { de_node = node; de_dvty = dvty; de_loc = loc }

(** Final stage *)

(** Binders *)

let binders bl =
  let sn = ref Sstr.empty in
  let binder (id, ghost, dity) =
    let id = match id with
      | Some ({pre_name = n} as id) ->
          let exn = match id.pre_loc with
            | Some loc -> Loc.Located (loc, Dterm.DuplicateVar n)
            | None -> Dterm.DuplicateVar n in
          sn := Sstr.add_new exn n !sn; id
      | None -> id_fresh "_" in
    create_pvsymbol id ~ghost (ity_of_dity dity) in
  List.map binder bl

(** Specifications *)

let to_fmla f = match f.t_ty with
  | None -> f
  | Some ty when ty_equal ty ty_bool -> t_equ f t_bool_true
  | _ -> Loc.error ?loc:f.t_loc Dterm.FmlaExpected

let create_assert = to_fmla

let create_invariant pl = List.map to_fmla pl

let create_pre = create_invariant

let create_post ty ql = List.map (fun (v,f) ->
  let f = (*Mlw_wp.remove_old*) (to_fmla f) in match v with
    | None -> Ity.create_post (create_vsymbol (id_fresh "result") ty) f
    | Some v -> Ty.ty_equal_check ty v.vs_ty; Ity.create_post v f) ql

let create_xpost xql =
  Mexn.mapi (fun xs ql -> create_post (ty_of_ity xs.xs_ity) ql) xql

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
        | Ityreg _, ({rs_field = Some _} as rs) -> v, ity, Some rs
        | _, {rs_cty={cty_args=[arg]; cty_result=res; cty_freeze=frz}} ->
            v, ity_full_inst (ity_match frz arg.pv_ity ity) res, None
        | _ -> quit () with Not_found -> quit () end
  | Tvar v ->
      let v = try restore_pv v with Not_found -> quit () in
      v, v.pv_ity, None
  | _ -> quit ()

let effect_of_dspec dsp =
  let add_raise xs _ eff = eff_raise eff xs in
  let eff = Mexn.fold add_raise dsp.ds_xpost eff_empty in
  let eff = if dsp.ds_diverge then eff_diverge eff else eff in
  let add_read s v = Spv.add (try restore_pv v with Not_found ->
    Loc.errorm "unsupported effect expression") s in
  let pvs = List.fold_left add_read Spv.empty dsp.ds_reads in
  let add_write (s,l,e) t = match effect_of_term t with
    | v, {ity_node = Ityreg reg}, fd ->
        let fs = match fd with
          | Some fd -> Spv.singleton (Opt.get fd.rs_field)
          | None -> Spv.of_list reg.reg_its.its_mfields in
        let wr = Loc.try3 ?loc:t.t_loc eff_write eff_empty reg fs in
        Spv.add v s, (wr,t)::l, eff_union e wr
    | _ ->
        Loc.errorm ?loc:t.t_loc "mutable expression expected" in
  List.fold_left add_write (pvs, [], eff) dsp.ds_writes

let e_find_eff pr e =
  try (e_find_minimal (fun e -> e.e_loc <> None && pr e.e_effect) e).e_loc
  with Not_found -> None

let check_spec dsp ecty e =
  let bad_write weff eff = not (Mreg.submap (fun _ s1 s2 -> Spv.subset s1 s2)
                                            weff.eff_writes eff.eff_writes) in
  let bad_raise xeff eff = not (Sexn.subset xeff.eff_raises eff.eff_raises) in
  (* computed effect vs user effect *)
  let check_rwd = dsp.ds_checkrw in
  let ur, uwrl, ue = effect_of_dspec dsp in
  let ucty = create_cty ecty.cty_args ecty.cty_pre
    ecty.cty_post ecty.cty_xpost ur ue ecty.cty_result in
  let ueff = ucty.cty_effect and urds = ucty.cty_reads in
  let eeff = ecty.cty_effect and erds = ecty.cty_reads in
  (* check that every user effect actually happens *)
  if not (Spv.subset urds erds) then Loc.errorm ?loc:e.e_loc
    "variable@ %a@ does@ not@ occur@ in@ this@ expression"
    Pretty.print_vs (Spv.choose (Spv.diff urds erds)).pv_vs;
  if bad_write ueff eeff then List.iter (fun (weff,t) ->
    if bad_write weff eeff then Loc.errorm ?loc:t.t_loc
      "this@ write@ effect@ does@ not@ happen@ in@ the@ expression") uwrl;
  if bad_raise ueff eeff then Loc.errorm ?loc:e.e_loc
    "this@ expression@ does@ not@ raise@ exception@ %a"
    print_xs (Sexn.choose (Sexn.diff ueff.eff_raises eeff.eff_raises));
  if ueff.eff_diverg && not eeff.eff_diverg then Loc.errorm ?loc:e.e_loc
    "this@ expression@ does@ not@ diverge";
  (* check that every computed effect is listed *)
  if check_rwd && not (Spv.subset erds urds) then Spv.iter (fun v ->
    Loc.errorm ?loc:e.e_loc
      "this@ expression@ depends@ on@ variable@ %a@ left@ out@ in@ \
      the@ specification" Pretty.print_vs v.pv_vs) (Spv.diff erds urds);
  if check_rwd && bad_write eeff ueff then
    Loc.errorm ?loc:(e_find_eff (fun eff -> bad_write eff ueff) e)
      "this@ expression@ produces@ an@ unlisted@ write@ effect";
  if ecty.cty_args <> [] && bad_raise eeff ueff then Sexn.iter (fun xs ->
    Loc.errorm ?loc:(e_find_eff (fun eff -> Sexn.mem xs eff.eff_raises) e)
      "this@ expression@ raises@ unlisted@ exception@ %a"
      print_xs xs) (Sexn.diff eeff.eff_raises ueff.eff_raises);
  if check_rwd && eeff.eff_diverg && not ueff.eff_diverg then
    Loc.errorm ?loc:(e_find_eff (fun eff -> eff.eff_diverg) e)
      "this@ expression@ may@ diverge,@ but@ this@ is@ not@ \
        stated@ in@ the@ specification"

let check_aliases recu c =
  let rds_regs = c.cty_freeze.isb_reg in
  let report r _ _ =
    if Mreg.mem r rds_regs then let spv = Spv.filter
        (fun v -> ity_r_occurs r v.pv_ity) c.cty_reads in
      Loc.errorm "The type of this function contains an alias with \
        external variable %a" print_pv (Spv.choose spv)
    else Loc.errorm "The type of this function contains an alias" in
  (* we allow the value in a non-recursive function to contain
     regions coming the function's arguments, but not from the
     context. It is sometimes useful to write a function around
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
  ignore (add_ity (if recu then regs else rds_regs) c.cty_result)

let check_fun rsym dsp e =
  let c,e = match e with
    | { e_node = Efun e; e_vty = VtyC c } -> c,e
    | _ -> invalid_arg "Dexpr.check_fun" in
  let c = match rsym with
    | Some s -> s.rs_cty
    | None -> c in
  check_spec dsp c e;
  check_aliases (rsym <> None) c

(** Environment *)

type env = {
  rsm : rsymbol Mstr.t;
  pvm : pvsymbol Mstr.t;
  vsm : vsymbol Mstr.t;
}

let env_empty = {
  rsm = Mstr.empty;
  pvm = Mstr.empty;
  vsm = Mstr.empty;
}

let add_rsymbol ({rsm = rsm} as env) rs =
  let n = rs.rs_name.id_string in
  { env with rsm = Mstr.add n rs rsm }

let add_pvsymbol ({pvm = pvm; vsm = vsm} as env) pv =
  let n = pv.pv_vs.vs_name.id_string in
  { env with pvm = Mstr.add n pv pvm; vsm = Mstr.add n pv.pv_vs vsm }

let add_pv_map ({pvm = pvm; vsm = vsm} as env) vm =
  let um = Mstr.map (fun pv -> pv.pv_vs) vm in
  { env with pvm = Mstr.set_union vm pvm; vsm = Mstr.set_union um vsm }

let add_binders env pvl = List.fold_left add_pvsymbol env pvl

(** Abstract values *)

let cty_of_spec env bl dsp dity =
  let ity = ity_of_dity dity in
  let ty = ty_of_ity ity in
  let bl = binders bl in
  let env = add_binders env bl in
  let dsp = dsp env.vsm ty in
  let rds,_,eff = effect_of_dspec dsp in
  let eff = refresh_of_effect eff in
  let p = create_pre dsp.ds_pre in
  let q = create_post ty dsp.ds_post in
  let xq = create_xpost dsp.ds_xpost in
  create_cty bl p q xq rds eff ity

let val_decl env (id,ghost,kind,bl,dsp,dity) =
  let ity = ity_of_dity dity in match kind with
  | RKlocal -> invalid_arg "Dexpr.val_decl"
  | _ when bl <> [] ->
      let c = cty_of_spec env bl dsp dity in
      ValS (create_rsymbol id ~ghost ~kind c)
  | _ when ity_immutable ity ->
      let c = cty_of_spec env bl dsp dity in
      if c.cty_pre <> [] then Loc.errorm
        "Top-level constants can have no preconditions";
      if not (Spv.is_empty c.cty_reads) then Loc.errorm
        "Top-level constants can have no external dependencies";
      if not (eff_is_empty c.cty_effect) then Loc.errorm
        "Top-level constants can produce no effects";
      ValS (create_rsymbol id ~ghost ~kind c)
  | RKnone when ity_closed ity ->
      let dsp = dsp env.vsm (ty_of_ity ity) in
      if dsp.ds_pre <> [] || dsp.ds_post <> [] ||
          not (Mexn.is_empty dsp.ds_xpost) || dsp.ds_reads <> [] ||
          dsp.ds_writes <> [] || dsp.ds_diverge || dsp.ds_checkrw then
        Loc.errorm "Mutable top-level variables can have no specification";
      ValV (create_pvsymbol id ~ghost ity)
  | RKnone -> Loc.errorm
      "Mutable top-level variables must have monomorphic type"
  | RKfunc -> Loc.errorm
      "Mutable top-level variables cannot be logical functions"
  | RKpred -> Loc.errorm
      "Mutable top-level variables cannot be logical predicates"
  | RKlemma -> Loc.errorm
      "Mutable top-level variables cannot be logical lemmas"

(** Expressions *)

(*
let implicit_post = Debug.register_flag "implicit_post"
  ~desc:"Generate@ a@ postcondition@ for@ pure@ functions@ without@ one."
*)

let warn_unused s loc =
  if s = "" || s.[0] <> '_' then
  Warning.emit ?loc "unused variable %s" s

let check_used_pv e pv = if not (Spv.mem pv e.e_vars) then
  warn_unused pv.pv_vs.vs_name.id_string pv.pv_vs.vs_name.id_loc

let rec strip uloc labs de = match de.de_node with
  | DEcast (de,_) -> strip uloc labs de
  | DEuloc (de,loc) -> strip (Some loc) labs de
  | DElabel (de,s) -> strip uloc (Slab.union labs s) de
  | _ -> uloc, labs, de

let set_loc ?(labs=Slab.empty) keep_loc loc uloc e =
  let loc = if uloc <> None then uloc else
            if keep_loc then loc else None in
  if loc = None && Slab.is_empty labs then e
  else e_label ?loc labs e

let rec expr ~keep_loc uloc env ffo ({de_loc = loc} as de) =
  let uloc, labs, de = strip uloc Slab.empty de in
  let e = Loc.try5 ?loc try_expr keep_loc uloc env ffo de in
  let e = match e.e_vty with
    | VtyC _ when ffo ->
        let dt = dity_of_dvty de.de_dvty in
        let ty = Loc.try1 ?loc ity_of_dity dt in
        let e = set_loc keep_loc loc uloc e in
        Loc.try4 ?loc e_app e [] [] ty
    | _ -> e in
  set_loc ~labs keep_loc loc uloc e

and try_expr keep_loc uloc env ffo ({de_dvty = argl,res} as de0) =
  let get env de = expr ~keep_loc uloc env true de in
  match de0.de_node with
  | DEvar (n,_) when argl = [] ->
      e_var (Mstr.find_exn (Dterm.UnboundVar n) n env.pvm)
  | DEvar (n,_) ->
      e_sym (Mstr.find_exn (Dterm.UnboundVar n) n env.rsm)
  | DEpv v ->
      e_var v
  | DErs s ->
      e_sym s
  | DEconst c ->
      e_const c
  | DEapp ({de_dvty = (_::_,_)} as de1, de2) ->
      (* it should be impossible for e1 to be a mapping *)
      let rec down de el = match de.de_node with
        | DEapp (de1, de2) -> down de1 (get env de2 :: el)
        | _ -> expr ~keep_loc uloc env false de, el in
      let e, el = down de1 [get env de2] in
      if argl = [] || not ffo
        then e_app e el (List.map ity_of_dity argl) (ity_of_dity res)
        else e_app e el [] (ity_of_dity (dity_of_dvty de0.de_dvty))
  | DEapp ({de_dvty = ([],_)} as de1, de2) ->
      (* it should be impossible for e1 to be a computation *)
      e_app (e_sym rs_func_app) [get env de1; get env de2] [] (ity_of_dity res)
  | DEfun (bl,dsp,de) ->
      let e, dsp, _ = expr_fun ~keep_loc uloc env (binders bl) dsp de in
      check_fun None dsp e;
      if bl <> [] then e else
        let e = set_loc keep_loc de0.de_loc uloc e in
        e_app e [] [] (cty_of_expr e).cty_result
  | DEany (bl,dsp,dity) ->
      let e = e_any (cty_of_spec env bl dsp dity) in
      if bl <> [] then e else
        let e = set_loc keep_loc de0.de_loc uloc e in
        e_app e [] [] (cty_of_expr e).cty_result
  | DElet ((id,ghost,kind,de1),de2) ->
      let e1 = expr ~keep_loc uloc env false de1 in
      let ld = create_let_defn id ~ghost ~kind e1 in
      let env = match ld.let_sym with
        | ValS s when s.rs_ghost && not ghost -> Loc.errorm ?loc:id.pre_loc
            "Function %s must be explicitly marked ghost" id.pre_name
        | ValS s -> add_rsymbol env s
        | ValV v -> add_pvsymbol env v in
      let e2 = expr ~keep_loc uloc env ffo de2 in
      let e2 =
        let e2_unit = match e2.e_vty with
          | VtyI i -> ity_equal i ity_unit
          | _ -> false in
        let id_in_e2 = match ld.let_sym with
          | ValV v -> Spv.mem v e2.e_vars
          | ValS s -> Srs.mem s e2.e_syms in
        if not id_in_e2 then warn_unused id.pre_name id.pre_loc;
        (* if e1 is a recursive call, we may not know yet its effects,
            so we have to rely on an heuristic: if the result of e1 is
            not used in e2, then it was probably called for the effect. *)
        let e1_no_eff = eff_is_pure e1.e_effect && id_in_e2 in
        if e2_unit (* e2 is unit *)
          && e2.e_ghost (* and e2 is ghost *)
          && not e1.e_ghost (* and e1 is non-ghost *)
          && not e1_no_eff (* and e1 has observable effects *)
        then
          let ld = create_let_defn (id_fresh "_") e2 in
          e_label ?loc:e2.e_loc Slab.empty (e_let ld e_void)
        else e2
      in
      e_let ld e2
  | DErec (drdf,de) ->
      let rdf = expr_rec ~keep_loc uloc env drdf in
      let add env fd = add_rsymbol env fd.fun_sym in
      let env = List.fold_left add env rdf.rec_defn in
      e_rec rdf (expr ~keep_loc uloc env ffo de)
  | DEnot de1 ->
      e_not (get env de1)
  | DElazy (op,de1,de2) ->
      e_lazy op (get env de1) (get env de2)
  | DEif (de1,de2,de3) ->
      e_if (get env de1) (get env de2) (get env de3)
  | DEcase (de1,bl) ->
      let e1 = get env de1 in
      let ity = ity_of_expr e1 in
      let ghost = e1.e_ghost in
      let branch (dp,de) =
        let vm, pat = create_prog_pattern dp.dp_pat ~ghost ity in
        let e = get (add_pv_map env vm) de in
        Mstr.iter (fun _ v -> check_used_pv e v) vm;
        pat, e in
      e_case e1 (List.map branch bl)
  | DEassign al ->
      let conv (de1,f,de2) = get env de1, f, get env de2 in
      e_assign (List.map conv al)
  | DEwhile (de1,dinv,dvarl,de2) ->
      let e1 = get env de1 in
      let e2 = get env de2 in
      let inv = dinv env.vsm in
      let varl = dvarl env.vsm in
      e_while e1 (create_invariant inv) varl e2
  | DEfor (id,de_from,dir,de_to,dinv,de) ->
      let e_from = get env de_from in
      let e_to = get env de_to in
      let v = create_pvsymbol id ity_int in
      let env = add_pvsymbol env v in
      let e = get env de in
      let inv = dinv env.vsm in
      e_for v e_from dir e_to (create_invariant inv) e
  | DEtry (de1,bl) ->
      let e1 = get env de1 in
      let add_branch (m,l) (xs,dp,de) =
        let vm, pat = create_prog_pattern dp.dp_pat xs.xs_ity in
        let e = get (add_pv_map env vm) de in
        Mstr.iter (fun _ v -> check_used_pv e v) vm;
        try Mexn.add xs ((pat,e) :: Mexn.find xs m) m, l
        with Not_found -> Mexn.add xs [pat,e] m, (xs::l) in
      let xsm, xsl = List.fold_left add_branch (Mexn.empty,[]) bl in
      let mk_branch xs = match Mexn.find xs xsm with
        | [{ pp_pat = { pat_node = Pvar v }}, e] ->
            xs, Ity.restore_pv v, e
        | [{ pp_pat = { pat_node = Pwild }}, e] ->
            xs, create_pvsymbol (id_fresh "_") xs.xs_ity, e
        | [{ pp_pat = { pat_node = Papp (fs,[]) }}, e]
          when ls_equal fs (Term.fs_tuple 0) ->
            xs, create_pvsymbol (id_fresh "_") xs.xs_ity, e
        | bl ->
            let v = create_pvsymbol (id_fresh "res") xs.xs_ity in
            let pl = List.rev_map (fun (p,_) -> [p.pp_pat]) bl in
            let bl = if Pattern.is_exhaustive [t_var v.pv_vs] pl then bl
              else let _,pp = create_prog_pattern PPwild v.pv_ity in
              (pp, e_raise xs (e_var v) (ity_of_dity res)) :: bl in
            xs, v, e_case (e_var v) (List.rev bl)
      in
      e_try e1 (List.rev_map mk_branch xsl)
  | DEraise (xs,de) ->
      e_raise xs (get env de) (ity_of_dity res)
  | DEghost de ->
      (* keep user ghost annotations even if redundant *)
      e_ghost (expr ~keep_loc uloc env ffo de)
  | DEassert (ak,f) ->
      e_assert ak (create_assert (f env.vsm))
  | DEpure t ->
      e_pure (t env.vsm)
  | DEabsurd ->
      e_absurd (ity_of_dity res)
  | DEtrue ->
      e_true
  | DEfalse ->
      e_false
  | DEmark _ -> assert false (* TODO *)
(*
  | DEmark (id,de) ->
      let ld,v = create_let_defn_pv id Mlw_wp.e_now in
      let env = add_pvsymbol env v in
      e_let ld (expr ~keep_loc uloc env env ffo de)
*)
  | DEcast _ | DEuloc _ | DElabel _ ->
      assert false (* already stripped *)

and expr_rec ~keep_loc uloc env {fds = dfdl} =
  let step1 env (id, gh, kind, bl, dsp, dvl, ({de_dvty = dvty} as de)) =
    let pvl = binders bl in
    let ity = Loc.try1 ?loc:de.de_loc ity_of_dity (dity_of_dvty dvty) in
    let cty = create_cty pvl [] [] Mexn.empty Spv.empty eff_empty ity in
    let rs = create_rsymbol id ~ghost:gh ~kind:RKnone cty in
    add_rsymbol env rs, (rs, kind, dsp, dvl, de) in
  let env, fdl = Lists.map_fold_left step1 env dfdl in
  let step2 ({rs_cty = c} as rs, kind, dsp, dvl, de) (fdl, dspl) =
    let lam, dsp, env = expr_fun ~keep_loc uloc env c.cty_args dsp de in
    if lam.e_ghost && not rs.rs_ghost then Loc.errorm ?loc:rs.rs_name.id_loc
      "Function %s must be explicitly marked ghost" rs.rs_name.id_string;
    (rs, lam, dvl env.vsm, kind)::fdl, dsp::dspl in
  (* check for unexpected aliases in case of trouble *)
  let fdl, dspl = try List.fold_right step2 fdl ([],[]) with
    | Loc.Located (_, Ity.TypeMismatch _) | Ity.TypeMismatch _ as exn ->
        List.iter (fun ({rs_name = {id_loc = loc}} as rs,_,_,_,_) ->
          Loc.try2 ?loc check_aliases true rs.rs_cty) fdl;
        raise exn in
  let rdf = try create_rec_defn fdl with
    | Loc.Located (_, Ity.TypeMismatch _) | Ity.TypeMismatch _ as exn ->
        List.iter (fun ({rs_name = {id_loc = loc}},lam,_,_) ->
          Loc.try2 ?loc check_aliases true (cty_of_expr lam)) fdl;
        raise exn in
  let check {fun_rsym = rs; fun_expr = e} dsp =
    Loc.try3 ?loc:rs.rs_name.id_loc check_fun (Some rs) dsp e in
  List.iter2 check rdf.rec_defn dspl;
  rdf

and expr_fun ~keep_loc uloc env pvl dsp de =
  let env = add_binders env pvl in
  let e = expr ~keep_loc uloc env true de in
  let ty = ty_of_ity (ity_of_expr e) in
  let dsp = dsp env.vsm ty in
  let p = create_pre dsp.ds_pre in
  let q = create_post ty dsp.ds_post in
  let xq = create_xpost dsp.ds_xpost in
  e_fun pvl p q xq e, dsp, env

let val_decl ?(keep_loc=true) (id,_,_,_,_,_ as vald) =
  reunify_regions ();
  Loc.try2 ?loc:id.pre_loc val_decl env_empty vald

let rec_defn ?(keep_loc=true) drdf =
  reunify_regions ();
  expr_rec ~keep_loc None env_empty drdf

let expr ?(keep_loc=true) de =
  reunify_regions ();
  let e = expr ~keep_loc None env_empty false de in
  check_expr e; e

let let_defn ?(keep_loc=true) (id,ghost,kind,de) =
  let e = expr ~keep_loc de in
  if e.e_ghost && not ghost then Loc.errorm ?loc:id.pre_loc
    "%s %s must be explicitly marked ghost" (match kind, e.e_vty with
      | RKnone, VtyI _ -> "Variable" | _ -> "Function") id.pre_name;
  Loc.try1 ?loc:id.pre_loc (create_let_defn id ~ghost ~kind) e
