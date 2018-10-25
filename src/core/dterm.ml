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

(** Types *)

type dty =
  | Dvar of dvar ref
  | Dapp of tysymbol * dty list
  | Duty of ty

and dvar =
  | Dind of int
  | Dval of dty

let dty_fresh = let i = ref 0 in fun () -> Dvar (ref (Dind (incr i; !i)))

let dty_of_ty ty = Duty ty

let dty_var tv = Duty (ty_var tv)

let rec dty_app ts dtl =
  try
    let tl = List.map (function Duty ty -> ty | _ -> raise Exit) dtl in
    Duty (ty_app ts tl)
  with Exit -> match ts.ts_def with
    | Alias ty ->
        let sbs = try List.fold_right2 Mtv.add ts.ts_args dtl Mtv.empty with
          | Invalid_argument _ -> raise (BadTypeArity (ts, List.length dtl)) in
        let rec inst ty = match ty.ty_node with
          | Tyapp (ts,tl) -> dty_app ts (List.map inst tl)
          | Tyvar v -> Mtv.find v sbs in
        inst ty
    | NoDef | Range _ | Float _ ->
        if List.length ts.ts_args <> List.length dtl then
          raise (BadTypeArity (ts, List.length dtl));
        Dapp (ts, dtl)

let dty_fold fnS fnV fnI dty =
  let rec on_ty ty = match ty.ty_node with
    | Tyapp (s, tl) -> fnS s (List.map on_ty tl)
    | Tyvar v -> fnV v in
  let rec on_dty = function
    | Dvar { contents = Dind i } -> fnI i
    | Dvar { contents = Dval dty } -> on_dty dty
    | Dapp (s, dtl) -> fnS s (List.map on_dty dtl)
    | Duty ty -> on_ty ty in
  on_dty dty

exception UndefinedTypeVar of tvsymbol

let rec ty_of_dty ~strict = function
  | Dvar { contents = Dval (Duty ty) } ->
      ty
  | Dvar ({ contents = Dval dty } as r) ->
      let ty = ty_of_dty ~strict dty in
      r := Dval (Duty ty); ty
  | Dvar r ->
      let tv = create_tvsymbol (id_fresh "xi") in
      let ty = ty_var tv in
      r := Dval (Duty ty);
      if strict then raise (UndefinedTypeVar tv) else ty
  | Dapp (ts,dl) ->
      ty_app ts (List.map (ty_of_dty ~strict) dl)
  | Duty ty -> ty

let rec occur_check i = function
  | Dvar { contents = Dval d } -> occur_check i d
  | Dvar { contents = Dind j } -> if i = j then raise Exit
  | Dapp (_,dl) -> List.iter (occur_check i) dl
  | Duty _ -> ()

let rec dty_match dty ty = match dty, ty.ty_node with
  | Dvar { contents = Dval dty }, _ -> dty_match dty ty
  | Dvar r, _ -> r := Dval (Duty ty)
  | Duty ty1, _ when ty_equal ty1 ty -> ()
  | Dapp (ts1,dl), Tyapp (ts2,tl) when ts_equal ts1 ts2 ->
      List.iter2 dty_match dl tl
  | _ -> raise Exit

let rec dty_unify dty1 dty2 = match dty1,dty2 with
  | Dvar { contents = Dval dty1 }, dty2
  | dty1, Dvar { contents = Dval dty2 } -> dty_unify dty1 dty2
  | Dvar { contents = Dind i },
    Dvar { contents = Dind j } when i = j -> ()
  | Dvar ({ contents = Dind i } as r), dty
  | dty, Dvar ({ contents = Dind i } as r) ->
      occur_check i dty; r := Dval dty
  | dty, Duty ty | Duty ty, dty -> dty_match dty ty
  | Dapp (ts1,dl1), Dapp (ts2,dl2) when ts_equal ts1 ts2 ->
      List.iter2 dty_unify dl1 dl2
  | _ -> raise Exit

let dty_int  = Duty ty_int
let dty_real = Duty ty_real
let dty_bool = Duty ty_bool

let protect_on x s = if x then "(" ^^ s ^^ ")" else s

let rec print_dty ht pri fmt = function
  | Dvar { contents = Dval dty } ->
      print_dty ht pri fmt dty
  | Dvar { contents = Dind i } ->
      let tv = try Hint.find ht i with Not_found ->
        let tv = create_tvsymbol (id_fresh "xi") in
        Hint.replace ht i tv; tv in
      Pretty.print_tv fmt tv
  | Dapp (ts,[d1;d2]) when ts_equal ts Ty.ts_func ->
      Format.fprintf fmt (protect_on (pri > 0) "%a@ ->@ %a")
        (print_dty ht 1) d1 (print_dty ht 0) d2
  | Dapp (ts,dl) when is_ts_tuple ts ->
      Format.fprintf fmt "(%a)"
        (Pp.print_list Pp.comma (print_dty ht 0)) dl
  | Dapp (ts,[]) ->
      Pretty.print_ts_qualified fmt ts
  | Dapp (ts,dl) ->
      Format.fprintf fmt (protect_on (pri > 1) "%a@ %a")
        Pretty.print_ts_qualified ts
        (Pp.print_list Pp.space (print_dty ht 2)) dl
  | Duty ({ty_node = Tyapp (ts,(_::_))} as ty)
    when (pri > 1 && not (is_ts_tuple ts))
      || (pri = 1 && ts_equal ts Ty.ts_func) ->
      Format.fprintf fmt "(%a)" Pretty.print_ty_qualified ty
  | Duty ty ->
      Pretty.print_ty_qualified fmt ty

let print_dty = let ht = Hint.create 3 in fun fmt dty ->
  print_dty ht 0 fmt dty

(** Symbols *)

let specialize_ls ls =
  let htv = Htv.create 3 in
  let find_tv tv = try Htv.find htv tv with Not_found ->
    let dtv = dty_fresh () in Htv.add htv tv dtv; dtv in
  let rec spec ty = match ty.ty_node with
    | Tyapp (ts, tyl) -> Dapp (ts, List.map spec tyl)
    | Tyvar tv -> find_tv tv in
  let spec ty = if ty_closed ty then Duty ty else spec ty in
  List.map spec ls.ls_args, Opt.map spec ls.ls_value

(* dead code
let specialize_fs ls =
  let dtyl, dty = specialize_ls ls in
  match dty with
  | Some dty -> dtyl, dty
  | None -> raise (FunctionSymbolExpected ls)
*)

let specialize_cs ls =
  if ls.ls_constr = 0 then raise (ConstructorExpected ls);
  let dtyl, dty = specialize_ls ls in
  dtyl, Opt.get dty

(* dead code
let specialize_ps ls =
  let dtyl, dty = specialize_ls ls in
  match dty with
  | Some _ -> raise (PredicateSymbolExpected ls)
  | None -> dtyl
*)

(** Patterns, terms, and formulas *)

type dpattern = {
  dp_node : dpattern_node;
  dp_dty  : dty;
  dp_vars : dty Mstr.t;
  dp_loc  : Loc.position option;
}

and dpattern_node =
  | DPwild
  | DPvar of preid
  | DPapp of lsymbol * dpattern list
  | DPor of dpattern * dpattern
  | DPas of dpattern * preid
  | DPcast of dpattern * dty

type dbinop =
  | DTand | DTand_asym | DTor | DTor_asym | DTimplies | DTiff | DTby | DTso

type dquant =
  | DTforall | DTexists | DTlambda

type dbinder = preid option * dty * Loc.position option

type dterm = {
  dt_node  : dterm_node;
  dt_dty   : dty option;
  dt_loc   : Loc.position option;
}

and dterm_node =
  | DTvar of string * dty
  | DTgvar of vsymbol
  | DTconst of Number.constant * dty
  | DTapp of lsymbol * dterm list
  | DTfapp of dterm * dterm
  | DTif of dterm * dterm * dterm
  | DTlet of dterm * preid * dterm
  | DTcase of dterm * (dpattern * dterm) list
  | DTeps of preid * dty * dterm
  | DTquant of dquant * dbinder list * dterm list list * dterm
  | DTbinop of dbinop * dterm * dterm
  | DTnot of dterm
  | DTtrue
  | DTfalse
  | DTcast of dterm * dty
  | DTuloc of dterm * Loc.position
  | DTattr of dterm * Sattr.t

(** Unification tools *)

exception TermExpected
exception FmlaExpected

let dty_unify_app ls unify (l1: 'a list) (l2: dty list) =
  try List.iter2 unify l1 l2 with Invalid_argument _ ->
    raise (BadArity (ls, List.length l1))

(* FIXME: can we convert every use of dty_unify_app to this one? *)
let dty_unify_app_map ls unify (l1: 'a list) (l2: dty list) =
  try List.map2 unify l1 l2 with Invalid_argument _ ->
    raise (BadArity (ls, List.length l1))

let dpat_expected_type dp dty =
  try dty_unify dp.dp_dty dty with Exit -> Loc.errorm ?loc:dp.dp_loc
    "This pattern has type %a,@ but is expected to have type %a"
    print_dty dp.dp_dty print_dty dty

let darg_expected_type ?loc dt_dty dty =
  try dty_unify dt_dty dty with Exit -> Loc.errorm ?loc
    "This term has type %a,@ but is expected to have type %a"
    print_dty dt_dty print_dty dty

let dterm_expected_type dt dty = match dt.dt_dty with
  | Some dt_dty -> darg_expected_type ?loc:dt.dt_loc dt_dty dty
  | None -> begin try dty_unify dty_bool dty with Exit ->
      Loc.error ?loc:dt.dt_loc TermExpected end

let dfmla_expected_type dt = match dt.dt_dty with
  | Some dt_dty -> begin try dty_unify dt_dty dty_bool with Exit ->
      Loc.error ?loc:dt.dt_loc FmlaExpected end
  | None -> ()

let dexpr_expected_type dt dty = match dty with
  | Some dty -> dterm_expected_type dt dty
  | None -> dfmla_expected_type dt

(** Environment *)

type denv = dterm_node Mstr.t

exception DuplicateVar of string
exception UnboundVar of string

let denv_get denv n = Mstr.find_exn (UnboundVar n) n denv

let denv_get_opt denv n = Mstr.find_opt n denv

let dty_of_dterm dt = Opt.get_def dty_bool dt.dt_dty

let denv_empty = Mstr.empty

let denv_add_var denv {pre_name = n} dty =
  Mstr.add n (DTvar (n, dty)) denv

let denv_add_let denv dt {pre_name = n} =
  Mstr.add n (DTvar (n, dty_of_dterm dt)) denv

let denv_add_quant denv vl =
  let add acc (id,dty,_) = match id with
    | Some ({pre_name = n} as id) ->
        let exn = match id.pre_loc with
          | Some loc -> Loc.Located (loc, DuplicateVar n)
          | None     -> DuplicateVar n in
        Mstr.add_new exn n (DTvar (n,dty)) acc
    | None -> acc in
  let s = List.fold_left add Mstr.empty vl in
  Mstr.set_union s denv

let denv_add_pat denv dp dty =
  dpat_expected_type dp dty;
  let s = Mstr.mapi (fun n dty -> DTvar (n, dty)) dp.dp_vars in
  Mstr.set_union s denv

let denv_add_term_pat denv dp dt =
  denv_add_pat denv dp (Opt.get_def dty_bool dt.dt_dty)

(** Constructors *)

let dpattern ?loc node =
  let get_dty = function
    | DPwild ->
        dty_fresh (), Mstr.empty
    | DPvar {pre_name = n} ->
        let dty = dty_fresh () in
        dty, Mstr.singleton n dty
    | DPapp (ls,dpl) ->
        let dtyl, dty = specialize_cs ls in
        (* FIXME: ignore (dty_unify_app_map ...) ? *)
        dty_unify_app ls dpat_expected_type dpl dtyl;
        let join n _ _ = raise (DuplicateVar n) in
        let add acc dp = Mstr.union join acc dp.dp_vars in
        dty, List.fold_left add Mstr.empty dpl
    | DPor (dp1,dp2) ->
        dpat_expected_type dp2 dp1.dp_dty;
        let join n dty1 dty2 = try dty_unify dty1 dty2; Some dty1
          with Exit -> Loc.errorm ?loc
            "Variable %s has type %a,@ but is expected to have type %a"
            n print_dty dty1 print_dty dty2 in
        dp1.dp_dty, Mstr.union join dp1.dp_vars dp2.dp_vars
    | DPas (dp,{pre_name = n}) ->
        dp.dp_dty, Mstr.add_new (DuplicateVar n) n dp.dp_dty dp.dp_vars
    | DPcast (dp,dty) ->
        dpat_expected_type dp dty;
        dty, dp.dp_vars in
  let dty, vars = Loc.try1 ?loc get_dty node in
  { dp_node = node; dp_dty = dty; dp_vars = vars; dp_loc = loc }

let coercion_attrs = Sattr.singleton Pretty.coercion_attr

let apply_coercion l ({dt_loc = loc} as dt) =
  let apply dt ls =
    let dtyl, dty = specialize_ls ls in
    dterm_expected_type dt (List.hd dtyl);
    let dt = { dt_node = DTapp (ls, [dt]); dt_dty = dty; dt_loc = loc } in
    { dt with dt_node = DTattr (dt, coercion_attrs) } in
  List.fold_left apply dt l

(* coercions using just head tysymbols without type arguments: *)
(* TODO: this can be improved *)
let rec ts_of_dty = function
  | Dvar {contents = Dval dty} ->
      ts_of_dty dty
  | Dvar {contents = Dind _}
  | Duty {ty_node = Tyvar _} ->
      raise Exit
  | Duty {ty_node = Tyapp (ts,_)}
  | Dapp (ts,_) ->
      ts

let ts_of_dty = function
  | Some dt_dty -> ts_of_dty dt_dty
  | None        -> ts_bool

(* NB: this function is not a morphism w.r.t.
   the identity of type variables. *)
let rec ty_of_dty_raw = function
  | Dvar { contents = Dval (Duty ty) } ->
     ty
  | Dvar ({ contents = Dval dty }) ->
     ty_of_dty_raw dty
  | Dvar _ ->
     ty_var (create_tvsymbol (id_fresh "xi"))
  | Dapp (ts,dl) ->
     ty_app ts (List.map (ty_of_dty_raw) dl)
  | Duty ty -> ty

let ty_of_dty_raw = function
  | Some dt_dty -> ty_of_dty_raw dt_dty
  | None        -> ty_bool

let max_dty crcmap dtl =
  let rec aux = function
    | (dty1, ts1, ty1) :: l ->
        (* find a type that cannot be coerced to another type *)
        let check (_, ts2, ty2) =
          try
            if not (ts_equal ts1 ts2) then
              ignore (Coercion.find crcmap ty1 ty2);
            true
          with Not_found -> false in
        (* by transitivity, we never have to look back *)
        if List.exists check l then aux l else dty1
    | [] -> assert false in
  let l = List.fold_left (fun acc { dt_dty = dty } ->
    try (dty, ts_of_dty dty, ty_of_dty_raw dty) :: acc
    with Exit -> acc) [] dtl in
  if l == [] then (List.hd dtl).dt_dty
  else aux l

let max_dty crcmap dtl =
  match max_dty crcmap dtl with
  | Some (Duty ty)
    when ty_equal ty ty_bool
    && List.exists (fun { dt_dty = dty } -> dty = None) dtl ->
      (* favor prop over bool *)
      None
  | dty -> dty

let dterm_expected crcmap dt dty =
  try
    let (ts1, ts2) = ts_of_dty dt.dt_dty, ts_of_dty dty in
    if (ts_equal ts1 ts2) then dt
    else
      let (ty1, ty2) = ty_of_dty_raw dt.dt_dty, ty_of_dty_raw dty in
      let crc = Coercion.find crcmap ty1 ty2 in
      apply_coercion crc dt
  with Not_found | Exit -> dt

let dexpr_expected_dexpr crcmap dt dty =
  let dt = dterm_expected crcmap dt dty in
  dexpr_expected_type dt dty;
  dt

let dterm_expected_dterm crcmap dt dty =
  dexpr_expected_dexpr crcmap dt (Some dty)

let dfmla_expected_dterm crcmap dt =
  dexpr_expected_dexpr crcmap dt None

let dterm crcmap ?loc node =
  let dterm_node loc node =
    let mk_dty ty = { dt_node = node; dt_dty = ty; dt_loc = loc } in
    match node with
    | DTvar (_,dty) ->
        mk_dty (Some dty)
    | DTgvar vs ->
        mk_dty (Some (dty_of_ty vs.vs_ty))
    | DTconst (_,dty) ->
        mk_dty (Some dty)
    | DTapp (ls, dtl) when ls_equal ls ps_equ ->
       let dtyl, dty = specialize_ls ls in
       let max = max_dty crcmap dtl in
       begin try dty_unify (Opt.get_def dty_bool max) (List.hd dtyl)
             with Exit -> () end;
       let dtl = dty_unify_app_map ls
                   (dterm_expected_dterm crcmap) dtl dtyl in
       { dt_node = DTapp (ls, dtl);
         dt_dty  = dty;
         dt_loc  = loc }
    | DTapp (ls, dtl) ->
        let dtyl, dty = specialize_ls ls in
        { dt_node = DTapp (ls,
            dty_unify_app_map ls (dterm_expected_dterm crcmap) dtl dtyl);
          dt_dty  = dty;
          dt_loc  = loc }
    | DTfapp ({dt_dty = Some _} as dt1, dt2) ->
        let dtyl, dty = specialize_ls fs_func_app in
        let dt1 = dterm_expected_dterm crcmap dt1 (List.hd dtyl) in
        { dt_node = DTapp (fs_func_app,
            dty_unify_app_map fs_func_app (dterm_expected_dterm crcmap) [dt1;dt2] dtyl);
          dt_dty  = dty;
          dt_loc  = loc }
    | DTfapp ({dt_dty = None; dt_loc = loc},_) ->
        Loc.errorm ?loc "This term has type bool,@ it cannot be applied"
    | DTif (df,dt1,dt2) ->
        let df = dfmla_expected_dterm crcmap df in
        let dty = max_dty crcmap [dt1;dt2] in
        let dt1 = dexpr_expected_dexpr crcmap dt1 dty in
        let dt2 = dexpr_expected_dexpr crcmap dt2 dty in
        { dt_node = DTif (df, dt1, dt2);
          dt_dty = dty;
          dt_loc = loc }
    | DTlet (dt,_,df) ->
        ignore (dty_of_dterm dt);
        mk_dty df.dt_dty
    | DTcase (_,[]) ->
        raise EmptyCase
    | DTcase (dt,bl) ->
        let dty = max_dty crcmap (List.map snd bl) in
        let bl = List.map (fun (pat,dt) -> pat, dexpr_expected_dexpr crcmap dt dty) bl in
        { dt_node = DTcase (dt,bl);
          dt_dty = dty;
          dt_loc = loc }
    | DTeps (_,dty,df) ->
        dfmla_expected_type df;
        mk_dty (Some dty)
    | DTquant (DTlambda,vl,_,df) ->
        let res = Opt.get_def dty_bool df.dt_dty in
        let app (_,l,_) r = Dapp (ts_func,[l;r]) in
        mk_dty (Some (List.fold_right app vl res))
    | DTquant ((DTforall|DTexists),_,_,df) ->
        dfmla_expected_type df;
        mk_dty None
    | DTbinop (_,df1,df2) ->
        dfmla_expected_type df1;
        dfmla_expected_type df2;
        mk_dty None
    | DTnot df ->
        dfmla_expected_type df;
        mk_dty None
    | DTtrue | DTfalse ->
        (* we put here [Some dty_bool] instead of [None] because we can
           always replace [true] by [True] and [false] by [False], so that
           there is no need to count these constructs as "formulas" which
           require explicit if-then-else conversion to bool *)
        mk_dty (Some dty_bool)
    | DTcast (dt,dty) ->
        dterm_expected_dterm crcmap dt dty
    | DTuloc (dt,_)
    | DTattr (dt,_) ->
        mk_dty (dt.dt_dty)
  in Loc.try1 ?loc (dterm_node loc) node

(** Final stage *)

let pat_ty_of_dty ~strict dty =
  if not strict then ty_of_dty ~strict dty else
  try ty_of_dty ~strict dty with UndefinedTypeVar tv -> Loc.errorm
    "This@ pattern@ has@ polymorphic@ type@ %a@ where@ type@ variable@ %a@ \
      is@ never@ named@ explicitly" print_dty dty Pretty.print_tv tv

let var_ty_of_dty {pre_loc = loc} ~strict dty =
  if not strict then ty_of_dty ~strict dty else
  try ty_of_dty ~strict dty with UndefinedTypeVar tv -> Loc.errorm ?loc
    "This@ variable@ has@ polymorphic@ type@ %a@ where@ type@ variable@ %a@ \
      is@ never@ named@ explicitly" print_dty dty Pretty.print_tv tv

let term_ty_of_dty ~strict dty =
  if not strict then ty_of_dty ~strict dty else
  try ty_of_dty ~strict dty with UndefinedTypeVar tv -> Loc.errorm
    "This@ term@ has@ polymorphic@ type@ %a@ where@ type@ variable@ %a@ \
      is@ never@ named@ explicitly" print_dty dty Pretty.print_tv tv

let pattern ~strict env dp =
  let acc = ref Mstr.empty in
  let find_var ({pre_name = n} as id) ty =
    try Mstr.find n !acc with Not_found ->
      let vs = create_vsymbol id ty in
      acc := Mstr.add n vs !acc; vs in
  let rec get dp =
    Loc.try2 ?loc:dp.dp_loc try_get dp.dp_dty dp.dp_node
  and try_get dty = function
    | DPwild ->
        pat_wild (pat_ty_of_dty ~strict dty)
    | DPvar id ->
        pat_var (find_var id (pat_ty_of_dty ~strict dty))
    | DPapp (ls,dpl) ->
        pat_app ls (List.map get dpl) (pat_ty_of_dty ~strict dty)
    | DPor (dp1,dp2) ->
        pat_or (get dp1) (get dp2)
    | DPas (dp,id) ->
        let pat = get dp in
        pat_as pat (find_var id pat.pat_ty)
    | DPcast (dp,_) ->
        get dp in
  let pat = get dp in
  Mstr.set_union !acc env, pat

let quant_vars ~strict env vl =
  let add acc (id,dty,loc) = match id with
    | Some ({pre_name = n} as id) ->
        let ty = var_ty_of_dty id ~strict dty in
        let vs = create_vsymbol id ty in
        let exn = match id.pre_loc with
          | Some loc -> Loc.Located (loc, DuplicateVar n)
          | None     -> DuplicateVar n in
        Mstr.add_new exn n vs acc, vs
    | None ->
        let ty = Loc.try1 ?loc (pat_ty_of_dty ~strict) dty in
        acc, create_vsymbol (id_fresh "_") ty in
  let acc, vl = Lists.map_fold_left add Mstr.empty vl in
  Mstr.set_union acc env, vl


let debug_ignore_unused_var = Debug.register_info_flag "ignore_unused_vars"
  ~desc:"Suppress@ warnings@ on@ unused@ variables"

let attr_w_unused_var_no =
  Ident.create_attribute "W:unused_variable:N"

let check_used_var t vs =
  if not (Sattr.mem attr_w_unused_var_no vs.vs_name.id_attrs) &&
      Debug.test_noflag debug_ignore_unused_var then
    begin
      let s = vs.vs_name.id_string in
      if (s = "" || s.[0] <> '_') && t_v_occurs vs t = 0 then
(*        Warning.emit ?loc:vs.vs_name.id_loc "unused variable %s" s*)
        ()
    end

let check_exists_implies f = match f.t_node with
  | Tbinop (Timplies,{ t_node = Tbinop (Tor,f,{ t_node = Ttrue }) },_)
    when Sattr.mem Term.asym_split f.t_attrs -> ()
  | Tbinop (Timplies,_,_) -> Warning.emit ?loc:f.t_loc
      "form \"exists x. P -> Q\" is likely an error (use \"not P \\/ Q\" if not)"
  | _ -> ()

let t_attr_set loc attrs t =
  if loc = None && Sattr.is_empty attrs
  then t else t_attr_set ?loc attrs t

let rec strip uloc attrs dt = match dt.dt_node with
  | DTcast (dt,_) -> strip uloc attrs dt
  | DTuloc (dt,loc) -> strip (Some loc) attrs dt
  | DTattr (dt,s) -> strip uloc (Sattr.union attrs s) dt
  | _ -> uloc, attrs, dt

let rec term ~strict ~keep_loc uloc env prop dt =
  let uloc, attrs, dt = strip uloc Sattr.empty dt in
  let tloc = if keep_loc then dt.dt_loc else None in
  let tloc = if uloc <> None then uloc else tloc in
  let t = Loc.try7 ?loc:dt.dt_loc
    try_term strict keep_loc uloc env prop dt.dt_dty dt.dt_node in
  let t = t_attr_set tloc attrs t in
  match t.t_ty with
  | Some _ when prop -> t_attr_set tloc Sattr.empty
      (Loc.try2 ?loc:dt.dt_loc t_equ t t_bool_true)
  | None when not prop -> t_attr_set tloc Sattr.empty
      (t_if t t_bool_true t_bool_false)
  | _ -> t

and try_term strict keep_loc uloc env prop dty node =
  let get env prop dt = term ~strict ~keep_loc uloc env prop dt in
  match node with
  | DTvar (n,_) ->
      t_var (Mstr.find_exn (UnboundVar n) n env)
  | DTgvar vs ->
      t_var vs
  | DTconst (c,dty) ->
      t_const c (term_ty_of_dty ~strict dty)
  | DTapp (ls,[]) when ls_equal ls fs_bool_true ->
      if prop then t_true else t_bool_true
  | DTapp (ls,[]) when ls_equal ls fs_bool_false ->
      if prop then t_false else t_bool_false
  | DTapp (ls,[dt1;dt2]) when ls_equal ls ps_equ ->
    (* avoid putting formulas into a term context *)
      if dt1.dt_dty = None || dt2.dt_dty = None
      then t_iff (get env true dt1) (get env true dt2)
      else t_equ (get env false dt1) (get env false dt2)
  | DTapp (ls,dtl) ->
      t_app ls (List.map (get env false) dtl)
        (Opt.map (term_ty_of_dty ~strict) dty)
  | DTfapp (dt1,dt2) ->
      t_func_app (get env false dt1) (get env false dt2)
  | DTlet (dt,id,df) ->
      let prop = prop || dty = None in
      let t = get env false dt in
      let v = create_vsymbol id (t_type t) in
      let env = Mstr.add id.pre_name v env in
      let f = get env prop df in
      check_used_var f v;
      t_let_close v t f
  | DTif (df,dt1,dt2) ->
      let prop = prop || dty = None in
      t_if (get env true df)
        (get env prop dt1) (get env prop dt2)
  | DTcase (dt,bl) ->
      let prop = prop || dty = None in
      let branch (dp,dt) =
        let env, p = pattern ~strict env dp in
        let t = get env prop dt in
        Svs.iter (check_used_var t) p.pat_vars;
        t_close_branch p t in
      t_case (get env false dt) (List.map branch bl)
  | DTeps (id,dty,df) ->
      let v = create_vsymbol id (var_ty_of_dty id ~strict dty) in
      let env = Mstr.add id.pre_name v env in
      let f = get env true df in
      check_used_var f v;
      t_eps_close v f
  | DTquant (q,vl,dll,df) ->
      let env, vl = quant_vars ~strict env vl in
      let prop = q <> DTlambda || df.dt_dty = None in
      let tr_get dt = get env (dt.dt_dty = None) dt in
      let trl = List.map (List.map tr_get) dll in
      let f = get env prop df in
      List.iter (check_used_var f) vl;
      begin match q with
        | DTforall ->
            t_forall_close vl trl f
        | DTexists ->
            check_exists_implies f;
            t_exists_close vl trl f
        | DTlambda ->
            t_lambda vl trl f
      end
  | DTbinop (DTand,df1,df2) ->
      t_and (get env true df1) (get env true df2)
  | DTbinop (DTand_asym,df1,df2) ->
      t_and_asym (get env true df1) (get env true df2)
  | DTbinop (DTor,df1,df2) ->
      t_or (get env true df1) (get env true df2)
  | DTbinop (DTor_asym,df1,df2) ->
      t_or_asym (get env true df1) (get env true df2)
  | DTbinop (DTimplies,df1,df2) ->
      t_implies (get env true df1) (get env true df2)
  | DTbinop (DTiff,df1,df2) ->
      t_iff (get env true df1) (get env true df2)
  | DTbinop (DTby,df1,df2) ->
      let t2 = get env true df2 in
      let tt = t_attr_set t2.t_loc Sattr.empty t_true in
      let t2 = t_attr_set t2.t_loc Sattr.empty (t_or_asym t2 tt) in
      t_implies t2 (get env true df1)
  | DTbinop (DTso,df1,df2) ->
      let t2 = get env true df2 in
      let tt = t_attr_set t2.t_loc Sattr.empty t_true in
      let t2 = t_attr_set t2.t_loc Sattr.empty (t_or_asym t2 tt) in
      t_and (get env true df1) t2
  | DTnot df ->
      t_not (get env true df)
  | DTtrue ->
      if prop then t_true else t_bool_true
  | DTfalse ->
      if prop then t_false else t_bool_false
  | DTcast _ | DTuloc _ | DTattr _ ->
      assert false (* already stripped *)

let fmla ?(strict=true) ?(keep_loc=true) dt =
  term ~strict ~keep_loc None Mstr.empty true dt

let term ?(strict=true) ?(keep_loc=true) dt =
  term ~strict ~keep_loc None Mstr.empty false dt

(** Exception printer *)

let () = Exn_printer.register (fun fmt e -> match e with
  | TermExpected ->
      Format.fprintf fmt "syntax error: term expected"
  | FmlaExpected ->
      Format.fprintf fmt "syntax error: formula expected"
  | DuplicateVar s ->
      Format.fprintf fmt "duplicate variable %s" s
  | UnboundVar s ->
      Format.fprintf fmt "unbound variable %s" s
  | _ -> raise e)
