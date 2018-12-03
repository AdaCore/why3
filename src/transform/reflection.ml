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

open Term
open Ty
open Decl
open Ident
open Task
open Args_wrapper
open Generic_arg_trans_utils

exception NoReification

let debug_reification = Debug.register_info_flag
                          ~desc:"Reification"
                          "reification"
let debug_refl = Debug.register_info_flag
                     ~desc:"Reflection transformations"
                     "reflection"

let expl_reification_check = Ident.create_attribute "expl:reification check"

type reify_env = { kn: known_map;
                   store: (vsymbol * int) Mterm.t;
                   fr: int;
                   subst: term Mvs.t;
                   lv: vsymbol list;
                   var_maps: ty Mvs.t; (* type of values pointed by each map*)
                   crc_map: Coercion.t;
                   ty_to_map: vsymbol Mty.t;
                   env: Env.env;
                   interps: Sls.t; (* functions that were inverted*)
                   task: Task.task;
                   bound_vars: Svs.t; (* bound variables, do not map them in a var map*)
                   bound_fr: int; (* separate, negative index for bound vars*)
                 }

let init_renv kn crc lv env task =
  { kn=kn;
    store = Mterm.empty;
    fr = 0;
    subst = Mvs.empty;
    lv = lv;
    var_maps = Mvs.empty;
    crc_map = crc;
    ty_to_map = Mty.empty;
    env = env;
    interps = Sls.empty;
    task = task;
    bound_vars = Svs.empty;
    bound_fr = -1;
  }

let rec reify_term renv t rt =
  let is_pvar p = match p.pat_node with Pvar _ -> true | _ -> false in
  let rec use_interp t =
    let r = match t.t_node with
      | Tconst _ -> true
      | Tvar _ -> false
      | Tapp (ls, []) ->
         begin match find_logic_definition renv.kn ls with
         | None -> false
         | Some ld ->
            let _,t = open_ls_defn ld in
            use_interp t
         end
      | Tapp (_, _) -> true
      | _ -> false in
    Debug.dprintf debug_reification "use_interp %a: %b@." Pretty.print_term t r;
    r in
  let add_to_maps renv vyl =
     let var_maps, ty_to_map =
       List.fold_left
         (fun (var_maps, ty_to_map) vy ->
           if Mty.mem vy.vs_ty ty_to_map
           then (Mvs.add vy vy.vs_ty var_maps, ty_to_map)
           else (Mvs.add vy vy.vs_ty var_maps,
                 Mty.add vy.vs_ty vy ty_to_map))
         (renv.var_maps, renv.ty_to_map)
         (List.map
            (fun t -> match t.t_node with Tvar vy -> vy | _ -> assert false)
            vyl)
     in
     { renv with var_maps = var_maps; ty_to_map = ty_to_map }
  in
  let open Theory in
  let th_list = Env.read_theory renv.env ["list"] "List" in
  let ty_list = ns_find_ts th_list.th_export ["list"] in
  let compat_h t rt =
    match t.t_node, rt.t_node with
    | Tapp (ls1,_), Tapp(ls2, _) -> ls_equal ls1 ls2
    | Tquant (Tforall, _), Tquant (Tforall, _)
      | Tquant (Texists, _), Tquant (Texists, _)-> true
    | _ -> false in
  let is_eq_true t = match t.t_node with
    | Tapp (eq, [_; tr])
       when ls_equal eq ps_equ && t_equal tr t_bool_true -> true
    | _ -> false in
  let lhs_eq_true t = match t.t_node with
    | Tapp (eq, [t; tr])
         when ls_equal eq ps_equ && t_equal tr t_bool_true -> t
    | _ -> assert false in
  let rec invert_nonvar_pat vl (renv:reify_env) (p,f) t =
    Debug.dprintf debug_reification
      "invert_nonvar_pat p %a f %a t %a@."
      Pretty.print_pat p Pretty.print_term f Pretty.print_term t;
    if is_eq_true f && not (is_eq_true t)
    then invert_nonvar_pat vl renv (p, lhs_eq_true f) t else
    match p.pat_node, f.t_node, t.t_node with
    | Pwild , _, _ | Pvar _,_,_ when t_equal_nt_na f t ->
       Debug.dprintf debug_reification "case equal@.";
       renv, t
    | Papp (cs, pl), _,_
         when compat_h f t
              && Svs.for_all (fun v -> t_v_occurs v f = 1) p.pat_vars
              && List.for_all is_pvar pl
                              (* could remove this with a bit more work in term reconstruction *)
      ->
       Debug.dprintf debug_reification "case app@.";
       let rec rt_of_var svs f t v (renv, acc) =
         assert (not (Mvs.mem v acc));
         Debug.dprintf debug_reification "rt_of_var %a %a@."
                                     Pretty.print_vs v Pretty.print_term f;
         if t_v_occurs v f = 1
            && Svs.for_all (fun v' -> vs_equal v v' || t_v_occurs v' f = 0) svs
         then let renv, rt = invert_pat vl renv (pat_var v, f) t in
              renv, Mvs.add v rt acc
         else
           match f.t_node, t.t_node with
           | Tapp(ls1, la1), Tapp(ls2, la2) when ls_equal ls1 ls2 ->
              let rec aux la1 la2 =
                match la1, la2 with
                | f'::l1, t'::l2 ->
                   if t_v_occurs v f' = 1 then rt_of_var svs f' t' v (renv, acc)
                   else aux l1 l2
                | _ -> assert false in
              aux la1 la2
           | Tquant (Tforall, tq1), Tquant (Tforall, tq2)
             | Tquant (Texists, tq1), Tquant (Texists, tq2) ->
              let _, _, t1 = t_open_quant tq1 in
              let vl, _, t2 = t_open_quant tq2 in
              let bv = List.fold_left Svs.add_left renv.bound_vars vl in
              let renv = { renv with bound_vars = bv } in
              rt_of_var svs t1 t2 v (renv, acc)
           | _ -> raise NoReification
       in
       let rec check_nonvar f t =
         match f.t_node, t.t_node with
         | Tapp (ls1, la1), Tapp (ls2, la2) ->
            if Svs.for_all (fun v -> t_v_occurs v f = 0) p.pat_vars
            then (if not (ls_equal ls1 ls2)
                  then raise NoReification);
            if ls_equal ls1 ls2 then List.iter2 check_nonvar la1 la2;
         | Tapp (ls,_), Tconst _ ->
            (* reject constants that do not match the
               definitions of logic constants*)
            if Svs.for_all (fun v -> t_v_occurs v f = 0) p.pat_vars
            then
              match find_logic_definition renv.kn ls with
              | None -> raise NoReification
              | Some ld -> let v,f = open_ls_defn ld in
                           assert (v = []);
                           check_nonvar f t
            else ()
         | Tconst (Number.ConstInt c1), Tconst (Number.ConstInt c2) ->
            let open Number in
            if not (BigInt.eq (compute_int_constant c1) (compute_int_constant c2))
            then raise NoReification
         | _ -> () (* FIXME add more failure cases if needed *)
       in
       check_nonvar f t;
       let renv, mvs = Svs.fold (rt_of_var p.pat_vars f t) p.pat_vars
                                (renv, Mvs.empty) in
       let lrt = List.map (function | {pat_node = Pvar v} -> Mvs.find v mvs
                                    | _ -> assert false) pl in
       renv, t_app cs lrt (Some p.pat_ty)
    | Pvar v, Tapp (ls1, la1), Tapp(ls2, la2)
         when ls_equal ls1 ls2 && t_v_occurs v f = 1
      -> Debug.dprintf debug_reification "case app_var@.";
         let renv, rt =
           List.fold_left2
             (fun (renv, acc) f t ->
               if acc = None
               then if t_v_occurs v f > 0
                    then let renv, rt = (invert_pat vl renv (p, f) t) in
                         renv, Some rt
                    else renv, acc
               else (assert (t_v_occurs v f = 0);
                     renv, acc))
             (renv,None) la1 la2 in
         renv, Opt.get rt
    | Pvar v, Tquant(Tforall, tq1), Tquant(Tforall, tq2)
      | Pvar v, Tquant(Texists, tq1), Tquant(Texists, tq2)
         when t_v_occurs v f = 1 ->
       Debug.dprintf debug_reification "case quant_var@.";
       let _,_,t1 = t_open_quant tq1 in
       let vl,_,t2 = t_open_quant tq2 in
       let bv = List.fold_left Svs.add_left renv.bound_vars vl in
       let renv = { renv with bound_vars = bv } in
       invert_nonvar_pat vl renv (p, t1) t2
    | Por (p1, p2), _, _ ->
       Debug.dprintf debug_reification "case or@.";
       begin try invert_pat vl renv (p1, f) t
             with NoReification -> invert_pat vl renv (p2, f) t
       end
    | Pvar _, Tvar _, Tvar _ | Pvar _, Tvar _, Tapp (_, [])
      | Pvar _, Tvar _, Tconst _
      -> Debug.dprintf debug_reification "case vars@.";
         (renv, t)
    | Pvar _, Tapp (ls, _hd::_tl), _
      -> Debug.dprintf debug_reification "case interp@.";
         invert_interp renv ls t
    | Papp (cs, [{pat_node = Pvar v}]), Tvar v', Tconst _
         when vs_equal v v'
      -> Debug.dprintf debug_reification "case var_const@.";
         renv, t_app cs [t] (Some p.pat_ty)
    | Papp (cs, [{pat_node = Pvar _}]), Tapp(ls, _hd::_tl), _
         when use_interp t (*FIXME*)
      -> Debug.dprintf debug_reification "case interp_var@.";
         let renv, rt = invert_interp renv ls t in
         renv, (t_app cs [rt] (Some p.pat_ty))
    | Papp _, Tapp (ls1, _), Tapp(ls2, _) ->
       Debug.dprintf debug_reification "head symbol mismatch %a %a@."
                                   Pretty.print_ls ls1 Pretty.print_ls ls2;
       raise NoReification
    | _ -> raise NoReification
  and invert_var_pat vl (renv:reify_env) (p,f) t =
    Debug.dprintf debug_reification
      "invert_var_pat p %a f %a t %a@."
      Pretty.print_pat p Pretty.print_term f Pretty.print_term t;
    match p.pat_node, f.t_node with
    | Papp (_, [{pat_node = Pvar v1}]),
      Tapp (ffa,[{t_node = Tvar vy}; {t_node = Tvar v2}])
      | Pvar v1, Tapp (ffa,[{t_node = Tvar vy}; {t_node = Tvar v2}])
         when ty_equal v1.vs_ty ty_int
              && Svs.mem v1 p.pat_vars
              && vs_equal v1 v2
              && ls_equal ffa fs_func_app
              && List.exists (fun vs -> vs_equal vs vy) vl (*FIXME*)
      ->
       Debug.dprintf debug_reification "case var@.";
       let rty = (Some p.pat_ty) in
       let app_pat trv = match p.pat_node with
         | Papp (cs, _) -> t_app cs [trv] rty
         | Pvar _ -> trv
         | _ -> assert false in
       let rec rm t =
         let t = match t.t_node with
           | Tapp (f,tl) -> t_app f (List.map rm tl) t.t_ty
           | Tvar _ | Tconst _ -> t
           | Tif (f,t1,t2) -> t_if (rm f) (rm t1) (rm t2)
           | Tbinop (op,f1,f2) -> t_binary op (rm f1) (rm f2)
           | Tnot f1 -> t_not (rm f1)
           | Ttrue | Tfalse -> t
           | _ -> t (* FIXME some cases missing *)
         in
         t_attr_set ?loc:t.t_loc Sattr.empty t
       in
       let t = rm t in
       (* remove attributes to identify terms modulo attributes *)
       if Mterm.mem t renv.store
       then
         begin
           Debug.dprintf debug_reification "%a exists@." Pretty.print_term t;
           (renv, app_pat (t_nat_const (snd (Mterm.find t renv.store))))
         end
       else
         begin
           Debug.dprintf debug_reification "%a is new@." Pretty.print_term t;
           let bound = match t.t_node with
             | Tvar v -> Svs.mem v renv.bound_vars
             | _ -> false in
           let renv, i=
             if bound
             then let i = renv.bound_fr in
                  { renv with bound_fr = i-1 }, i
             else
               let vy = Mty.find vy.vs_ty renv.ty_to_map in
               let fr = renv.fr in
               let store = Mterm.add t (vy, fr) renv.store in
               { renv with store = store; fr = fr + 1 }, fr in
           let const = Number.(ConstInt (int_const_of_int i)) in
           (renv, app_pat (t_const const Ty.ty_int))
         end
    | _ -> raise NoReification
  and invert_pat vl renv (p,f) t =
    if (oty_equal f.t_ty t.t_ty)
    then
      try invert_nonvar_pat vl renv (p,f) t
      with NoReification -> invert_var_pat vl renv (p,f) t
    else begin
        try
          let crc = Coercion.find renv.crc_map
                                  (Opt.get t.t_ty) (Opt.get f.t_ty) in
          let apply_crc t ls = t_app_infer ls [t] in
          let crc_t = List.fold_left apply_crc t crc in
          assert (oty_equal f.t_ty crc_t.t_ty);
          invert_pat vl renv (p,f) crc_t
        with Not_found ->
          Debug.dprintf debug_reification "type mismatch between %a and %a@."
            Pretty.print_ty (Opt.get f.t_ty)
            Pretty.print_ty (Opt.get t.t_ty);
          raise NoReification
      end
  and invert_interp renv ls (t:term) =
    let ld = try Opt.get (find_logic_definition renv.kn ls)
             with Invalid_argument _ ->
               Debug.dprintf debug_reification
                 "did not find def of %a@."
                 Pretty.print_ls ls;
               raise NoReification
    in
    let vl, f = open_ls_defn ld in
    Debug.dprintf debug_reification "invert_interp ls %a t %a@."
                                Pretty.print_ls ls Pretty.print_term t;
    invert_body { renv with interps = Sls.add ls renv.interps } ls vl f t
  and invert_body renv ls vl f t =
    match f.t_node with
    | Tvar v when vs_equal v (List.hd vl) -> renv, t
    | Tif (f, th, el) when t_equal th t_bool_true && t_equal el t_bool_false ->
       invert_body renv ls vl f t
    | Tcase (x, bl)
      ->
       (match x.t_node with
        | Tvar v when vs_equal v (List.hd vl) -> ()
        | _ -> Debug.dprintf debug_reification "not matching on first param@.";
               raise NoReification);
       Debug.dprintf debug_reification "case match@.";
       let rec aux invert = function
         | [] -> raise NoReification
         | tb::l ->
            try invert vl renv (t_open_branch tb) t
            with NoReification ->
                 Debug.dprintf debug_reification "match failed@."; aux invert l in
       (try aux invert_nonvar_pat bl with NoReification -> aux invert_var_pat bl)
    | Tapp (ls', _) ->
       Debug.dprintf debug_reification "case app@.";
       invert_interp renv ls' t
    | _ -> Debug.dprintf debug_reification "function body not handled@.";
           Debug.dprintf debug_reification "f: %a@." Pretty.print_term f;
           raise NoReification
  and invert_ctx_interp renv ls t l g =
    let ld = try Opt.get (find_logic_definition renv.kn ls)
             with Invalid_argument _ ->
               Debug.dprintf debug_reification "did not find def of %a@."
                 Pretty.print_ls ls;
               raise NoReification
    in
    let vl, f = open_ls_defn ld in
    Debug.dprintf debug_reification "invert_ctx_interp ls %a @."
                                Pretty.print_ls ls;
    let renv = { renv with interps = Sls.add ls renv.interps } in
    invert_ctx_body renv ls vl f t l g
  and invert_ctx_body renv ls vl f t l g =
    match f.t_node with
    | Tcase ({t_node = Tvar v}, [tbn; tbc] ) when vs_equal v (List.hd vl) ->
       let ty_g = g.vs_ty in
       let ty_list_g = ty_app ty_list [ty_g] in
       if (not (ty_equal ty_list_g l.vs_ty))
       then (Debug.dprintf debug_reification
               "bad type for context interp function@.";
             raise NoReification);
       let nil = ns_find_ls th_list.th_export ["Nil"] in
       let cons = ns_find_ls th_list.th_export ["Cons"] in
       let (pn, fn) = t_open_branch tbn in
       let (pc, fc) = t_open_branch tbc in
       begin match pn.pat_node, fn.t_node, pc.pat_node, fc.t_node with
       | Papp(n, []),
         Tapp(eq'', [{t_node=Tapp(leq,{t_node = Tvar g'}::_)};btr'']),
         Papp (c, [{pat_node = Pvar hdl};{pat_node = Pvar tll}]),
         Tbinop(Timplies,
                {t_node=(Tapp(eq, [({t_node = Tapp(leq', _)} as thd); btr]))},
                {t_node = (Tapp(eq',
                    [({t_node =
                         Tapp(ls', {t_node = Tvar tll'}::{t_node=Tvar g''}::_)}
                         as ttl); btr']))})
            when ls_equal n nil && ls_equal c cons && ls_equal ls ls'
                 && vs_equal tll tll'
                 && vs_equal g' g'' && ls_equal leq leq'
                 && List.mem g' vl
                 && not (Mvs.mem tll (t_vars thd))
                 && not (Mvs.mem hdl (t_vars ttl))
                 && ls_equal eq ps_equ && ls_equal eq' ps_equ
                 && ls_equal eq'' ps_equ && t_equal btr t_bool_true
                 && t_equal btr' t_bool_true && t_equal btr'' t_bool_true
         ->
          Debug.dprintf debug_reification "reifying goal@.";
          let (renv, rg) = invert_interp renv leq t in
          let renv = { renv with subst = Mvs.add g rg renv.subst } in
          Debug.dprintf debug_reification "filling context@.";
          let rec add_to_ctx (renv, ctx) e =
            try
              match e.t_node with
              | Teps _ -> (renv, ctx)
              | Tbinop (Tand,e1,e2) ->
                 add_to_ctx (add_to_ctx (renv, ctx) e1) e2
              | _ ->
                 let (renv,req) = invert_interp renv leq e in
                 (renv,(t_app cons [req; ctx] (Some ty_list_g)))
            with
            | NoReification -> renv,ctx
          in
          let renv, ctx =
              task_fold
                (fun (renv,ctx) td ->
                  match td.td_node with
                  | Decl {d_node = Dprop (Paxiom, _, e)}
                    -> add_to_ctx (renv, ctx) e
                  | Decl {d_node = Dlogic [ls, ld]} when ls.ls_args = []
                    ->
                     add_to_ctx (renv, ctx) (ls_defn_axiom ld)
                  | _-> renv,ctx)
                             (renv, (t_app nil [] (Some ty_list_g))) renv.task in
          { renv with subst = Mvs.add l ctx renv.subst }
       | _ -> Debug.dprintf debug_reification "unhandled interp structure@.";
              raise NoReification
       end
    | Tif (c, th, el) when t_equal th t_bool_true && t_equal el t_bool_false ->
       invert_ctx_body renv ls vl c t l g
    | _ -> Debug.dprintf debug_reification "not a match on list@.";
           raise NoReification
  in
  Debug.dprintf debug_reification "reify_term t %a rt %a@."
    Pretty.print_term t Pretty.print_term rt;
  if not (oty_equal t.t_ty rt.t_ty)
  then (Debug.dprintf debug_reification "reification type mismatch %a %a@."
          Pretty.print_ty (Opt.get t.t_ty)
          Pretty.print_ty (Opt.get rt.t_ty);
        raise NoReification);
  match t.t_node, rt.t_node with
  | _, Tapp(interp, {t_node = Tvar vx}::vyl)
       when List.mem vx renv.lv
            && List.for_all
                 (fun t -> match t.t_node with
                           | Tvar vy -> List.mem vy renv.lv
                           | _ -> false)
                 vyl  ->
     Debug.dprintf debug_reification "case interp@.";
     let renv = add_to_maps renv vyl in
     let renv, x = invert_interp renv interp t in
     { renv with subst = Mvs.add vx x renv.subst }
  | Tapp(eq, [t1; t2]), Tapp (eq', [rt1; rt2])
       when ls_equal eq ps_equ && ls_equal eq' ps_equ
            && oty_equal t1.t_ty rt1.t_ty && oty_equal t2.t_ty rt2.t_ty
    ->
     Debug.dprintf debug_reification "case eq@.";
     reify_term (reify_term renv t1 rt1) t2 rt2
  | _, Tapp(eq,[{t_node=Tapp(interp, {t_node = Tvar l}::{t_node = Tvar g}::vyl)}; tr])
       when ls_equal eq ps_equ && t_equal tr t_bool_true
            && ty_equal (ty_app ty_list [g.vs_ty]) l.vs_ty
            && List.mem l renv.lv
            && List.mem g renv.lv
            && List.for_all
                 (fun t -> match t.t_node with
                           | Tvar vy -> List.mem vy renv.lv
                           | _ -> false)
                 vyl
    ->
     Debug.dprintf debug_reification "case context@.";
     let renv = add_to_maps renv vyl in
     invert_ctx_interp renv interp t l g
  | Tbinop(Tiff,t,{t_node=Ttrue}), Tapp(eq,[{t_node=Tapp(interp, {t_node = Tvar f}::vyl)}; tr])
       when ls_equal eq ps_equ && t_equal tr t_bool_true
            && t.t_ty=None ->
     Debug.dprintf debug_reification "case interp_fmla@.";
     Debug.dprintf debug_reification "t %a rt %a@." Pretty.print_term t Pretty.print_term rt;
     let renv = add_to_maps renv vyl in
     let renv, rf = invert_interp renv interp t in
     { renv with subst = Mvs.add f rf renv.subst }
  | _ -> Debug.dprintf debug_reification "no reify_term match@.";
         Debug.dprintf debug_reification "lv = [%a]@."
                                     (Pp.print_list Pp.space Pretty.print_vs)
                                     renv.lv;
         raise NoReification

let build_vars_map renv prev =
  Debug.dprintf debug_reification "building vars map@.";
  let subst, prev = Mvs.fold
                (fun vy ty_vars (subst, prev) ->
                  Debug.dprintf debug_reification "creating var map %a@."
                    Pretty.print_vs vy;
                  let ly = create_fsymbol (Ident.id_fresh vy.vs_name.id_string)
                             [] ty_vars in
                  let y = t_app ly [] (Some ty_vars) in
                  let d = create_param_decl ly in
                  let prev = Task.add_decl prev d in
                  Mvs.add vy y subst, prev)
                renv.var_maps (renv.subst, prev) in
  let prev, mapdecls =
    Mvs.fold
      (fun vy _ (prev,prs) ->
        Debug.dprintf debug_reification "checking %a@." Pretty.print_vs vy;
        let vs = Mty.find vy.vs_ty renv.ty_to_map in
        if vs_equal vy vs then prev,prs
        else begin
            Debug.dprintf debug_reification "aliasing %a and %a@."
              Pretty.print_vs vy Pretty.print_vs vs;
            let y = Mvs.find vy subst in
            let z = Mvs.find vs subst in
            let et = t_equ y z in
            let pr = create_prsymbol (Ident.id_fresh "map_alias") in
            let d = create_prop_decl Paxiom pr et in
            Task.add_decl prev d, pr::prs end)
      renv.var_maps (prev, []) in
  if not (List.for_all (fun v -> Mvs.mem v subst) renv.lv)
  then (Debug.dprintf debug_reification "vars not matched: %a@."
          (Pp.print_list Pp.space Pretty.print_vs)
          (List.filter (fun v -> not (Mvs.mem v subst)) renv.lv);
        raise (Arg_error "vars not matched"));
  Debug.dprintf debug_reification "all vars matched@.";
  let prev, defdecls =
    Mterm.fold
      (fun t (vy,i) (prev,prs) ->
        let y = Mvs.find vy subst in
        let et = t_equ
                   (t_app fs_func_app [y; t_nat_const i]
                          t.t_ty)
                   t in
        Debug.dprintf debug_reification "%a %d = %a@."
                                    Pretty.print_vs vy i Pretty.print_term t;
        let s = Format.sprintf "y_val%d" i in
        let pr = create_prsymbol (Ident.id_fresh s) in
        let d = create_prop_decl Paxiom pr et in
        Task.add_decl prev d, pr::prs)
      renv.store (prev,[]) in
  subst, prev, mapdecls, defdecls

let build_goals do_trans renv prev mapdecls defdecls subst env lp g rt =
  Debug.dprintf debug_refl "building goals@.";
  let inst_rt = t_subst subst rt in
  Debug.dprintf debug_refl "reified goal instantiated@.";
  let inst_lp = List.map (t_subst subst) lp in
  Debug.dprintf debug_refl "premises instantiated@.";
  let hr = create_prsymbol (id_fresh "HR") in
  let d_r = create_prop_decl Paxiom hr inst_rt in
  let pr = create_prsymbol
             (id_fresh "GR"
                       ~attrs:(Sattr.singleton expl_reification_check)) in
  let d = create_prop_decl Pgoal pr g in
  let task_r = Task.add_decl (Task.add_decl prev d_r) d in
  Debug.dprintf debug_refl "building cut indication rt %a g %a@."
    Pretty.print_term rt Pretty.print_term g;
  let compute_hyp_few pr = Compute.normalize_hyp_few None (Some pr) env in
  let compute_in_goal = Compute.normalize_goal_transf_all env in
  let ltask_r =
    try let ci =
          match (rt.t_node, g.t_node) with
          | (Tapp(eq, rh::rl),
             Tapp(eq', h::l))
               when ls_equal eq eq' ->
             List.fold_left2
               (fun ci st rst ->
                 t_and ci (t_equ (t_subst subst rst) st))
               (t_equ (t_subst subst rh) h)
               l rl
          | _,_ when g.t_ty <> None -> t_equ (t_subst subst rt) g
          | _ -> raise Not_found in
        Debug.dprintf debug_refl "cut ok@.";
        Trans.apply (Cut.cut ci (Some "interp")) task_r
    with Arg_trans _ | TypeMismatch _ | Not_found ->
         Debug.dprintf debug_refl "no cut found@.";
         if do_trans
         then
           let g, prev = task_separate_goal task_r in
           let prev = Sls.fold
                     (fun ls t ->
                       Task.add_meta t Compute.meta_rewrite_def [Theory.MAls ls])
                     renv.interps prev in
           let t = Task.add_tdecl prev g in
           let t = Trans.apply (compute_hyp_few hr) t in
           match t with
           | [t] ->
              let rewrite = Apply.rewrite_list false true
                              (mapdecls@defdecls) (Some hr) in
              Trans.apply rewrite t
           | [] -> []
           | _ -> assert false
         else [task_r] in
  let lt = List.map (fun ng -> Task.add_decl prev
                       (create_prop_decl Pgoal (create_prsymbol (id_fresh "G")) ng))
                    inst_lp in
  let lt = if do_trans
           then Lists.apply (Trans.apply compute_in_goal) lt
           else lt in
  Debug.dprintf debug_refl "done@.";
  ltask_r@lt

let reflection_by_lemma pr env : Task.task Trans.tlist = Trans.store (fun task ->
  let kn = task_known task in
  let g, prev = Task.task_separate_goal task in
  let g = Apply.term_decl g in
  Debug.dprintf debug_refl "start@.";
  let l =
    let kn' = task_known prev in (* TODO Do we want kn here ? *)
    match find_prop_decl kn' pr with
    | (_, t) -> t
    | exception Not_found -> raise (Arg_error "lemma not found")
  in
  let (lp, lv, llet, rt) = Apply.intros l in
  if llet <> []
  then begin
      (* TODO handle lets *)
      Debug.dprintf debug_refl "let in procedure postcondition@.";
      raise NoReification
    end;
  let nt = Args_wrapper.build_naming_tables task in
  let crc = nt.Trans.coercion in
  let renv = reify_term (init_renv kn crc lv env prev) g rt in
  let subst, prev, mds, dds = build_vars_map renv prev in
  build_goals true renv prev mds dds subst env lp g rt)

open Expr
open Ity
open Wstdlib
open Mlinterp

exception ReductionFail of reify_env

let reflection_by_function do_trans s env = Trans.store (fun task ->
  Debug.dprintf debug_refl "reflection_f start@.";
  let kn = task_known task in
  let nt = Args_wrapper.build_naming_tables task in
  let crc = nt.Trans.coercion in
  let g, prev = Task.task_separate_goal task in
  let g = Apply.term_decl g in
  let ths = Task.used_theories task in
  let o =
    Mid.fold
      (fun _ th o ->
        try
          let pmod = Pmodule.restore_module th in
          let rs = Pmodule.ns_find_rs pmod.Pmodule.mod_export [s] in
          if o = None then Some (pmod, rs)
          else (let es = Format.sprintf "module or function %s found twice" s in
                raise (Arg_error es))
        with Not_found -> o)
      ths None in
  let (_pmod, rs) = if o = None
                    then (let es = Format.sprintf "Symbol %s not found@." s in
                          raise (Arg_error es))
                   else Opt.get o in
  let lpost = List.map open_post rs.rs_cty.cty_post in
  if List.exists (fun pv -> pv.pv_ghost) rs.rs_cty.cty_args
  then (Debug.dprintf debug_refl "ghost parameter@.";
        raise (Arg_error "function has ghost parameters"));
  Debug.dprintf debug_refl "building module map@.";
  let mm = Mid.fold
             (fun id th acc ->
               try
                 let pm = Pmodule.restore_module th in
                 Mstr.add id.id_string pm acc
               with Not_found -> acc)
             ths Mstr.empty in
  Debug.dprintf debug_refl "module map built@.";
  let args = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
  let rec reify_post = function
    | [] -> Debug.dprintf debug_refl "no postcondition reifies@.";
            raise NoReification
    | (vres, p)::t -> begin
        try
          Debug.dprintf debug_refl "new post@.";
          Debug.dprintf debug_refl "post: %a, %a@."
            Pretty.print_vs vres Pretty.print_term p;
          let (lp, lv, llet, rt) = Apply.intros p in
          if llet <> []
          then begin
              (* TODO handle lets *)
              Debug.dprintf debug_refl "let in procedure postcondition@.";
              raise NoReification
            end;
          let lv = lv @ args in
          let renv = reify_term (init_renv kn crc lv env prev) g rt in
          Debug.dprintf debug_refl "computing args@.";
          let vars =
            List.fold_left
              (fun vars (vs, t) ->
                if List.mem vs args
                then begin
                    Debug.dprintf debug_refl "value of term %a for arg %a@."
                                                Pretty.print_term t
                                                Pretty.print_vs vs;
                    Mid.add vs.vs_name (value_of_term kn t) vars end
                else vars)
              Mid.empty
              (Mvs.bindings renv.subst) in
          Debug.dprintf debug_refl "evaluating@.";
          let res =
            try term_of_value (Mlinterp.interp env mm rs vars)
            with Raised (xs,_,cs) ->
              Format.eprintf "Raised %s %a@." (xs.xs_name.id_string)
                (Pp.print_list Pp.semi Expr.print_rs) cs;
              raise (ReductionFail renv) in
          Debug.dprintf debug_refl "res %a@." Pretty.print_term res;
          let rinfo = {renv with subst = Mvs.add vres res renv.subst} in
          rinfo, lp, lv, rt
        with NoReification -> reify_post t
      end
  in
  try
    let rinfo, lp, _lv, rt = reify_post lpost in
    let lp = (rs.rs_cty.cty_pre)@lp in
    let subst, prev, mds, dds = build_vars_map rinfo prev in
    build_goals do_trans rinfo prev mds dds subst env lp g rt
  with
    ReductionFail renv ->
    (* proof failed, show reification context for debugging *)
    let _, prev, _, _ = build_vars_map renv prev in
    let fg = create_prsymbol (id_fresh "Failure") in
    let df = create_prop_decl Pgoal fg t_false in
    [Task.add_decl prev df] )

let () = wrap_and_register
           ~desc:"reflection_l <prop> attempts to prove the goal by reflection using the lemma prop"
           "reflection_l"
           (Tprsymbol Tenvtrans_l) reflection_by_lemma

let () = wrap_and_register
           ~desc:"reflection_f <f> attempts to prove the goal by reflection using the contract of the program function f"
           "reflection_f"
           (Tstring Tenvtrans_l) (reflection_by_function true)

let () = wrap_and_register
           ~desc:"reflection_f <f> attempts to prove the goal by reflection using the contract of the program function f, does not automatically perform transformations afterward. Use for debugging."
           "reflection_f_nt"
           (Tstring Tenvtrans_l) (reflection_by_function false)
(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
