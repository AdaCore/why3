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

(* destructive types for program type inference *)

open Ident
open Ty
open Term
open Ptree
open Mlw_ty
open Mlw_ty.T
open Mlw_expr

type dity =
  | Dvar  of dvar ref
  | Duvar of tvsymbol
  | Dits  of itysymbol * dity list * dreg list
  | Dts   of tysymbol  * dity list

and dvar =
  | Dtvs  of tvsymbol
  | Dval  of dity

and dreg =
  | Rreg  of region * dity
  | Rvar  of rvar ref

and rvar =
  | Rtvs  of tvsymbol * dity * region Lazy.t
  | Rval  of dreg

let ity_of_dity dity =
  let rec get_ity = function
    | Dvar { contents = Dtvs _ } ->
        Loc.errorm "undefined type variable"
    | Dvar { contents = Dval dty } -> get_ity dty
    | Duvar tv -> ity_var tv
    | Dits (its,dl,rl) ->
        ity_app its (List.map get_ity dl) (List.map get_reg rl)
    | Dts (ts,dl) -> ity_pur ts (List.map get_ity dl)
  and get_reg = function
    | Rreg (r,_) -> r
    | Rvar { contents = Rtvs (_,_,r) } -> Lazy.force r
    | Rvar { contents = Rval dreg } -> get_reg dreg
  in
  get_ity dity

let create_user_type_variable x =
  Duvar (Typing.create_user_tv x.id)

let create_type_variable () =
  Dvar (ref (Dtvs (create_tvsymbol (id_fresh "a"))))

let create_dreg dity =
  let id = id_fresh "rho" in
  let tv = create_tvsymbol id in
  let reg = lazy (create_region id (ity_of_dity dity)) in
  Rvar (ref (Rtvs (tv,dity,reg)))

let ts_app_real ts dl = Dts (ts, dl)

let its_app_real its dl rl = Dits (its, dl, rl)

let rec ity_inst_fresh mv mr ity = match ity.ity_node with
  | Ityvar v ->
      mr, Mtv.find v mv
  | Itypur (s,tl) ->
      let mr,tl = Lists.map_fold_left (ity_inst_fresh mv) mr tl in
      mr, ts_app_real s tl
  | Ityapp (s,tl,rl) ->
      let mr,tl = Lists.map_fold_left (ity_inst_fresh mv) mr tl in
      let mr,rl = Lists.map_fold_left (reg_refresh mv) mr rl in
      mr, its_app_real s tl rl

and reg_refresh mv mr r = match Mreg.find_opt r mr with
  | Some r ->
      mr, r
  | None ->
      let mr,ity = ity_inst_fresh mv mr r.reg_ity in
      let reg = create_dreg ity in
      Mreg.add r reg mr, reg

let its_app s tl =
  let add m v t = Mtv.add v t m in
  let mv = try List.fold_left2 add Mtv.empty s.its_ts.ts_args tl
    with Invalid_argument _ ->
      raise (BadItyArity (s, List.length s.its_ts.ts_args, List.length tl)) in
  match s.its_def with
  | Some ity ->
      snd (ity_inst_fresh mv Mreg.empty ity)
  | None ->
      let _,rl = Lists.map_fold_left (reg_refresh mv) Mreg.empty s.its_regs in
      its_app_real s tl rl

let ts_app ts dl =
  let add m v t = Mtv.add v t m in
  let mv = try List.fold_left2 add Mtv.empty ts.ts_args dl
    with Invalid_argument _ ->
      raise (BadTypeArity (ts, List.length ts.ts_args, List.length dl)) in
  match ts.ts_def with
  | Some ty ->
      snd (ity_inst_fresh mv Mreg.empty (ity_of_ty ty))
  | None ->
      ts_app_real ts dl

(* unification *)

let rec occur_check tv = function
  | Dvar { contents = Dval d } -> occur_check tv d
  | Dits (_,dl,_) | Dts (_,dl) -> List.iter (occur_check tv) dl
  | Dvar { contents = Dtvs tv' } | Duvar tv' ->
      if tv_equal tv tv' then raise Exit

let rec occur_check_reg tv = function
  | Dvar { contents = Dval d } -> occur_check_reg tv d
  | Dvar { contents = Dtvs _ } | Duvar _ -> ()
  | Dits (_,dl,rl) ->
      let rec check = function
        | Rvar { contents = Rval dreg } -> check dreg
        | Rvar { contents = Rtvs (tv',dity,_) } ->
            if tv_equal tv tv' then raise Exit;
            occur_check_reg tv dity
        | Rreg _ -> ()
      in
      List.iter (occur_check_reg tv) dl;
      List.iter check rl
  | Dts (_,dl) ->
      List.iter (occur_check_reg tv) dl

let rec unify ~weak d1 d2 = match d1,d2 with
  | Dvar { contents = Dval d1 }, d2
  | d1, Dvar { contents = Dval d2 } ->
      unify ~weak d1 d2
  | Dvar { contents = Dtvs tv1 },
    Dvar { contents = Dtvs tv2 } when tv_equal tv1 tv2 ->
      ()
  | Dvar ({ contents = Dtvs tv } as r), d
  | d, Dvar ({ contents = Dtvs tv } as r) ->
      occur_check tv d; r := Dval d
  | Duvar tv1, Duvar tv2 when tv_equal tv1 tv2 -> ()
  | Dits (its1, dl1, rl1), Dits (its2, dl2, rl2) when its_equal its1 its2 ->
      assert (List.length rl1 = List.length rl2);
      assert (List.length dl1 = List.length dl2);
      List.iter2 (unify ~weak) dl1 dl2;
      if not weak then List.iter2 unify_reg rl1 rl2
  | Dts (ts1, dl1), Dts (ts2, dl2) when ts_equal ts1 ts2 ->
      assert (List.length dl1 = List.length dl2);
      List.iter2 (unify ~weak) dl1 dl2
  | _ -> raise Exit

and unify_reg r1 r2 =
  let rec dity_of_reg = function
    | Rvar { contents = Rval r } -> dity_of_reg r
    | Rvar { contents = Rtvs (_,dity,_) }
    | Rreg (_,dity) -> dity
  in
  match r1,r2 with
    | Rvar { contents = Rval r1 }, r2
    | r1, Rvar { contents = Rval r2 } ->
        unify_reg r1 r2
    | Rvar { contents = Rtvs (tv1,_,_) },
      Rvar { contents = Rtvs (tv2,_,_) } when tv_equal tv1 tv2 ->
        ()
    | Rvar ({ contents = Rtvs (tv,rd,_) } as r), d
    | d, Rvar ({ contents = Rtvs (tv,rd,_) } as r) ->
        let dity = dity_of_reg d in
        occur_check_reg tv dity;
        unify ~weak:false rd dity;
        r := Rval d
    | Rreg (reg1,_), Rreg (reg2,_) when reg_equal reg1 reg2 -> ()
    | _ -> raise Exit

exception DTypeMismatch of dity * dity

let unify ~weak d1 d2 =
  try unify ~weak d1 d2 with Exit -> raise (DTypeMismatch (d1,d2))

let unify_weak d1 d2 = unify ~weak:true d1 d2
let unify d1 d2 = unify ~weak:false d1 d2

type dvty = dity list * dity (* A -> B -> C == ([A;B],C) *)

let vty_of_dvty (argl,res) =
  let ity_of_dity dity = ity_of_dity dity in
  let vtv = VTvalue (vty_value (ity_of_dity res)) in
  let conv a = create_pvsymbol (id_fresh "x") (vty_value (ity_of_dity a)) in
  if argl = [] then vtv else VTarrow (vty_arrow (List.map conv argl) vtv)

type tvars = dity list

let empty_tvars = []

let add_dity tvs dity = dity :: tvs
let add_dvty tvs (argl,res) = res :: List.rev_append argl tvs

let tv_in_tvars tv tvs =
  try List.iter (occur_check tv) tvs; false with Exit -> true

let reg_in_tvars tv tvs =
  try List.iter (occur_check_reg tv) tvs; false with Exit -> true

let specialize_scheme tvs (argl,res) =
  let htvs = Htv.create 17 in
  let hreg = Htv.create 17 in
  let rec specialize = function
    | Dvar { contents = Dval d } -> specialize d
    | Dvar { contents = Dtvs tv } | Duvar tv as d ->
        if tv_in_tvars tv tvs then d else
        begin try Htv.find htvs tv with Not_found ->
          let v = create_type_variable () in
          Htv.add htvs tv v; v
        end
    | Dits (its, dl, rl) ->
        its_app_real its (List.map specialize dl) (List.map spec_reg rl)
    | Dts (ts, dl) ->
        ts_app_real ts (List.map specialize dl)
  and spec_reg r = match r with
    | Rvar { contents = Rval r } -> spec_reg r
    | Rvar { contents = Rtvs (tv,dity,_) } ->
        if reg_in_tvars tv tvs then r else
        begin try Htv.find hreg tv with Not_found ->
          let v = create_dreg (specialize dity) in
          Htv.add hreg tv v; v
        end
    | Rreg _ -> r
  in
  List.map specialize argl, specialize res

(* Specialization of symbols *)

let rec dity_of_ity htv hreg vars ity = match ity.ity_node with
  | Ityvar tv ->
      assert (not (Stv.mem tv vars.vars_tv));
      begin try Htv.find htv tv with Not_found ->
        let dtv = create_type_variable () in
        Htv.add htv tv dtv;
        dtv
      end
  | Itypur (ts, ityl) ->
      ts_app_real ts (List.map (dity_of_ity htv hreg vars) ityl)
  | Ityapp (its, ityl, rl) ->
      its_app_real its (List.map (dity_of_ity htv hreg vars) ityl)
        (List.map (dreg_of_reg htv hreg vars) rl)

and dreg_of_reg htv hreg vars r =
  try Hreg.find hreg r with Not_found ->
  let dity = dity_of_ity htv hreg vars r.reg_ity in
  let dreg = if reg_occurs r vars then Rreg (r,dity)
    else create_dreg dity in
  Hreg.add hreg r dreg;
  dreg

let dity_of_vtv htv hreg vars v = dity_of_ity htv hreg vars v.vtv_ity

let specialize_vtvalue vtv =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  dity_of_vtv htv hreg vtv.vtv_ity.ity_vars vtv

let specialize_pvsymbol pv =
  specialize_vtvalue pv.pv_vtv

let specialize_xsymbol xs =
  specialize_vtvalue (vty_value xs.xs_ity)

let specialize_vtarrow vars vta =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  let conv pv = dity_of_vtv htv hreg vars pv.pv_vtv in
  let rec specialize a =
    let argl = List.map conv a.vta_args in
    let narg,res = match a.vta_result with
      | VTvalue v -> [], dity_of_vtv htv hreg vars v
      | VTarrow a -> specialize a
    in
    argl @ narg, res
  in
  specialize vta

let specialize_psymbol ps =
  specialize_vtarrow ps.ps_vars ps.ps_vta

let specialize_plsymbol pls =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  let conv vtv = dity_of_vtv htv hreg vars_empty vtv in
  List.map conv pls.pl_args, conv pls.pl_value

let dity_of_ty htv hreg vars ty =
  dity_of_ity htv hreg vars (ity_of_ty ty)

let specialize_lsymbol ls =
  let htv = Htv.create 3 and hreg = Hreg.create 3 in
  let conv ty = dity_of_ty htv hreg vars_empty ty in
  let ty = Opt.get_def ty_bool ls.ls_value in
  List.map conv ls.ls_args, conv ty

(* Pretty-printing *)

let debug_print_reg_types = Debug.register_info_flag "print_reg_types"
  ~desc:"Print@ types@ of@ regions@ (mutable@ fields)."

let print_dity fmt dity =
  let protect_on x s = if x then "(" ^^ s ^^ ")" else s in
  let rec print_dity inn fmt = function
    | Dvar { contents = Dtvs tv }
    | Duvar tv ->
        Pretty.print_tv fmt tv
    | Dvar { contents = Dval dty } ->
        print_dity inn fmt dty
    | Dts (ts,tl) when is_ts_tuple ts ->
        Format.fprintf fmt "(%a)"
          (Pp.print_list Pp.comma (print_dity false)) tl
    | Dts (ts,[]) ->
        Pretty.print_ts fmt ts
    | Dts (ts,tl) ->
        Format.fprintf fmt (protect_on inn "%a@ %a")
          Pretty.print_ts ts (Pp.print_list Pp.space (print_dity true)) tl
    | Dits (its,[],rl) ->
        Format.fprintf fmt (protect_on inn "%a@ <%a>")
          Mlw_pretty.print_its its (Pp.print_list Pp.comma print_dreg) rl
    | Dits (its,tl,rl) ->
        Format.fprintf fmt (protect_on inn "%a@ <%a>@ %a")
          Mlw_pretty.print_its its (Pp.print_list Pp.comma print_dreg) rl
          (Pp.print_list Pp.space (print_dity true)) tl
  and print_dreg fmt = function
    | Rreg (r,_) when Debug.test_flag debug_print_reg_types ->
        Format.fprintf fmt "@[%a:@,%a@]" Mlw_pretty.print_reg r
          Mlw_pretty.print_ity r.reg_ity
    | Rreg (r,_) ->
        Mlw_pretty.print_reg fmt r
    | Rvar { contents = Rtvs (tv,dity,_) }
      when Debug.test_flag debug_print_reg_types ->
        let r = create_region (id_clone tv.tv_name) Mlw_ty.ity_unit in
        Format.fprintf fmt "@[%a:@,%a@]" Mlw_pretty.print_reg r
          (print_dity false) dity
    | Rvar { contents = Rtvs (tv,_,_) } ->
        let r = create_region (id_clone tv.tv_name) Mlw_ty.ity_unit in
        Mlw_pretty.print_reg fmt r
    | Rvar { contents = Rval dreg } ->
        print_dreg fmt dreg
  in
  print_dity false fmt dity

let () = Exn_printer.register
  begin fun fmt exn -> match exn with
  | DTypeMismatch (t1,t2) ->
      Format.fprintf fmt "Type mismatch between %a and %a"
        print_dity t1 print_dity t2
  | _ -> raise exn
  end
