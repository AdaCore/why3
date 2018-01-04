open Term
open Ty
open Decl
open Ident
open Task
open Args_wrapper

let rec fold_left3 f accu l1 l2 l3 =
  match (l1, l2, l3) with
  | a1::l1, a2::l2, a3::l3 -> fold_left3 f (f accu a1 a2 a3) l1 l2 l3
  | [], [], [] -> accu
  | _ -> raise (Invalid_argument "fold_left3")

exception NoReification
exception Exit

let debug = true

let expl_reification_check = Ident.create_label "expl:reification check"

type reify_env = { kn: known_map;
                   store: (vsymbol * int) Mterm.t;
                   fr: int;
                   subst: term Mvs.t;
                   lv: vsymbol list;
                   var_maps: ty Mvs.t; (* type of values pointed by each map*)
                   ty_to_map: vsymbol Mty.t;
                   env: Env.env;
                   task: Task.task;
                 }

let init_renv kn lv env task =
  { kn=kn;
    store = Mterm.empty;
    fr = 0;
    subst = Mvs.empty;
    lv = lv;
    var_maps = Mvs.empty;
    ty_to_map = Mty.empty;
    env = env;
    task = task;
  }

let rec is_const t =
  let r = match t.t_node with
  | Tconst _ -> true
  | Tvar _ -> false
  | Tapp (_, []) -> false
  | Tapp (_, l) -> List.for_all is_const l
  | _ -> false in
  if debug then Format.printf "is_const %a: %b@." Pretty.print_term t r;
  r

let rec reify_term renv t rt =
  let is_pvar p = match p.pat_node with Pvar _ -> true | _ -> false in
  let rec find_var vl v p (renv, acc) f t =
    if acc = None
    then if t_v_occurs v f > 0
         then let renv, rt = (invert_pat vl renv (p, f) t) in
              renv, Some rt
         else renv, acc
    else (assert (t_v_occurs v f = 0);
          renv, acc)
  and invert_nonvar_pat vl (renv:reify_env) (p,f) t =
    if debug
    then Format.printf
           "invert_nonvar_pat p %a f %a t %a@."
           Pretty.print_pat p Pretty.print_term f Pretty.print_term t;
    match p.pat_node, f.t_node, t.t_node with
    | Pwild , _, _ | Pvar _,_,_ when t_equal_nt_nl f t ->
       if debug then Format.printf "case equal@.";
       renv, t
    (*| Papp (cs, pl), Tapp(ls1, la1), Tapp(ls2, la2)
         when ls_equal ls1 ls2 && List.length pl = List.length la1
      ->
       if debug then Format.printf "case app@.";
       (* same head symbol, match parameters *)
       let renv, rl =
         fold_left3
           (fun (renv, acc) p f t ->
             let renv, nt = invert_pat vl renv (p, f) t in
             if debug
             then Format.printf "param %a matched@." Pretty.print_term t;
             (renv, nt::acc))
           (renv, []) pl la1 la2 in
       if debug then Format.printf "building app %a of type %a with args %a@."
                                   Pretty.print_ls cs
                                   Pretty.print_ty p.pat_ty
                                   (Pp.print_list Pp.comma Pretty.print_term)
                                   (List.rev rl);
       let t = t_app cs (List.rev rl) (Some p.pat_ty) in
       if debug then Format.printf "app ok@.";
       renv, t*)
    | Papp (cs, pl), Tapp(ls1, _), Tapp(ls2, _)
         when ls_equal ls1 ls2
              && Svs.for_all (fun v -> t_v_occurs v f = 1) p.pat_vars
              && List.for_all is_pvar pl
              (* could remove this with a bit more work in term reconstruction *)
      ->
       if debug then Format.printf "case app@.";
       let rec rt_of_var svs f t v (renv, acc) =
         assert (not (Mvs.mem v acc));
         if debug then Format.printf "rt_of_var %a %a@."
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
           | _ -> raise NoReification
       in
       let renv, mvs = Svs.fold (rt_of_var p.pat_vars f t) p.pat_vars (renv, Mvs.empty) in
       let lrt = List.map (function | {pat_node = Pvar v} -> Mvs.find v mvs
                                    | _ -> assert false) pl in
       renv, t_app cs lrt (Some p.pat_ty)
    | Pvar v, Tapp (ls1, la1), Tapp(ls2, la2)
         when ls_equal ls1 ls2 && t_v_occurs v f = 1
      -> if debug then Format.printf "case app_var@.";
         let renv, rt =
           List.fold_left2 (find_var vl v p) (renv, None) la1 la2 in
         (*(fun (renv, acc) f t ->
               if acc = None
               then if t_v_occurs v f > 0
                    then let renv, rt = (invert_pat vl renv (p, f) t) in
                         renv, Some rt
                    else renv, acc
               else (assert (t_v_occurs v f = 0);
                     renv, acc))
             (renv,None) la1 la2
         in*)
         renv, Opt.get rt
    (*| Papp(cs, [({pat_node = Pvar v} as vp)]), Tapp (ls1, la1), Tapp(ls2, la2)
         when ls_equal ls1 ls2 && t_v_occurs v f = 1
      -> if debug then Format.printf "case capp_var@.";
         let renv, rt =
           List.fold_left2 (find_var vl v vp) (renv, None) la1 la2 in
         renv, t_app cs [(Opt.get rt)] (Some p.pat_ty)*)
    | Por (p1, p2), _, _ ->
       if debug then Format.printf "case or@.";
       begin try invert_pat vl renv (p1, f) t
             with NoReification -> invert_pat vl renv (p2, f) t
       end
    | Pvar _, Tvar _, Tvar _ | Pvar _, Tvar _, Tapp (_, [])
      | Pvar _, Tvar _, Tconst _
      -> if debug then Format.printf "case vars@.";
         (renv, t)
    | Pvar _, Tapp (ls, _hd::_tl), _
      -> if debug then Format.printf "case interp@.";
         invert_interp renv ls t
    | Papp (cs, [{pat_node = Pvar _}]), Tapp(ls, _hd::_tl), _
         when is_const t
      -> if debug then Format.printf "case interp_const@.";
         let renv, rt = invert_interp renv ls t in
         renv, (t_app cs [rt] (Some p.pat_ty))
    | Papp (cs, [{pat_node = Pvar v}]), Tvar v', Tconst _
         when vs_equal v v'
      -> if debug then Format.printf "case var_const@.";
         renv, t_app cs [t] (Some p.pat_ty)
    | Papp _, Tapp (ls1, _), Tapp(ls2, _) ->
       if debug then Format.printf "head symbol mismatch %a %a@."
                                   Pretty.print_ls ls1 Pretty.print_ls ls2;
       raise NoReification
    | _ -> raise NoReification
  and invert_var_pat vl (renv:reify_env) (p,f) t =
    if debug
    then Format.printf
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
       if debug then Format.printf "case var@.";
       let rty = (Some p.pat_ty) in
       let app_pat trv = match p.pat_node with
         | Papp (cs, _) -> t_app cs [trv] rty
         | Pvar _ -> trv
         | _ -> assert false in
       let t = t_label ?loc:t.t_loc Slab.empty t in
       (* remove labels to identify terms that are equal modulo labels *)
       if Mterm.mem t renv.store
       then
         begin
           if debug then Format.printf "%a exists@." Pretty.print_term t;
           (renv, app_pat (t_nat_const (snd (Mterm.find t renv.store))))
         end
       else
         begin
           if debug then Format.printf "%a is new@." Pretty.print_term t;
           let fr = renv.fr in
           let vy = Mty.find vy.vs_ty renv.ty_to_map in
           let store = Mterm.add t (vy, fr) renv.store in
           let renv = { renv with store = store; fr = fr + 1 } in
           (renv, app_pat (t_nat_const fr))
         end
    | _ -> raise NoReification
  and invert_pat vl renv (p,f) t =
    (if not (oty_equal f.t_ty t.t_ty)
     then
       (if debug
        then Format.printf "type mismatch between %a and %a@."
                           Pretty.print_ty (Opt.get f.t_ty)
                           Pretty.print_ty (Opt.get t.t_ty);
        raise NoReification)); (*FIXME at least check coercions ?*)
    try invert_nonvar_pat vl renv (p,f) t
    with NoReification -> invert_var_pat vl renv (p,f) t
  and invert_interp renv ls (t:term) = (*la ?*)
    let ld = try Opt.get (find_logic_definition renv.kn ls)
             with _ ->
                  if debug
                  then Format.printf "did not find def of %a@." Pretty.print_ls ls;
                  raise NoReification
    in
    let vl, f = open_ls_defn ld in
    if debug then Format.printf "invert_interp ls %a t %a@."
                                Pretty.print_ls ls Pretty.print_term t;
    invert_body renv ls vl f t
  and invert_body renv ls vl f t =
    match f.t_node with
    | Tvar v when vs_equal v (List.hd vl) -> renv, t
    | Tif (f, th, el) when t_equal th t_bool_true && t_equal el t_bool_false ->
       invert_body renv ls vl f t
    | Tcase (x, bl)
      ->
       (match x.t_node with
        | Tvar v when vs_equal v (List.hd vl) -> ()
        | _ -> if debug then Format.printf "not matching on first param@.";
               raise NoReification);
       if debug then Format.printf "case match@.";
       let rec aux invert = function
         | [] -> raise NoReification
         | tb::l ->
            try invert vl renv (t_open_branch tb) t
            with NoReification ->
                 if debug then Format.printf "match failed@."; aux invert l in
       (try aux invert_nonvar_pat bl with NoReification -> aux invert_var_pat bl)
    | _ -> if debug then Format.printf "function body not handled@.";
           if debug then Format.printf "f: %a@." Pretty.print_term f;
           raise NoReification
  and invert_ctx_interp renv ls t l g =
    let ld = try Opt.get (find_logic_definition renv.kn ls)
             with _ ->
                  if debug
                  then Format.printf "did not find def of %a@." Pretty.print_ls ls;
                  raise NoReification
    in
    let vl, f = open_ls_defn ld in
    if debug then Format.printf "invert_ctx_interp ls %a @."
                                Pretty.print_ls ls;
    invert_ctx_body renv ls vl f t l g
  and invert_ctx_body renv ls vl f t l g =
    match f.t_node with
    | Tcase ({t_node = Tvar v}, [tbn; tbc] ) when vs_equal v (List.hd vl) ->
       let open Theory in
       let th_list = Env.read_theory renv.env ["list"] "List" in
       let ty_g = g.vs_ty in
       let ty_list = ns_find_ts th_list.th_export ["list"] in
       let ty_list_g = ty_app ty_list [ty_g] in
       if (not (ty_equal ty_list_g l.vs_ty))
       then (if debug
             then Format.printf "bad type for context interp function@.";
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
          if debug then Format.printf "reifying goal@.";
          let (renv, rg) = invert_interp renv leq t in
          let renv = { renv with subst = Mvs.add g rg renv.subst } in
          if debug then Format.printf "filling context@.";
          let renv, ctx =
              task_fold
                (fun (renv,ctx) td ->
                  match td.td_node with
                  | Decl {d_node = Dprop (Paxiom, _, e)}
                    ->
                     begin try
                         (match e.t_node with
                          | Tquant _ | Teps _ | Tbinop _ -> renv, ctx
                          | _ ->
                             let (renv,req) = invert_interp renv leq e in
                             (renv,(t_app cons [req; ctx] (Some ty_list_g))))
                       with
                       | NoReification -> renv,ctx
                                                 (* | TypeMismatch _ -> raise NoReification*)
                     end
                  | _-> renv,ctx)
                             (renv, (t_app nil [] (Some ty_list_g))) renv.task in
          { renv with subst = Mvs.add l ctx renv.subst }
       | _ -> if debug then Format.printf "unhandled interp structure@.";
              raise NoReification
       end
    | Tif (c, th, el) when t_equal th t_bool_true && t_equal el t_bool_false ->
       invert_ctx_body renv ls vl c t l g
    | _ -> if debug then Format.printf "not a match on list@.";
           raise NoReification
  in
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
  if debug then Format.printf "reify_term t %a rt %a@."
                              Pretty.print_term t Pretty.print_term rt;
  if not (oty_equal t.t_ty rt.t_ty)
  then (if debug
        then Format.printf "reification type mismatch %a %a@."
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
     if debug then Format.printf "case interp@.";
     let renv = add_to_maps renv vyl in
     let renv, x = invert_interp renv interp t in
     { renv with subst = Mvs.add vx x renv.subst }
  | Tapp(eq, [t1; t2]), Tapp (eq', [rt1; rt2])
       when ls_equal eq ps_equ && ls_equal eq' ps_equ
            && oty_equal t1.t_ty rt1.t_ty && oty_equal t2.t_ty rt2.t_ty
    ->
     if debug then Format.printf "case eq@.";
     reify_term (reify_term renv t1 rt1) t2 rt2
  | _, Tapp(eq,[{t_node=Tapp(interp, {t_node = Tvar l}::{t_node = Tvar g}::vyl)}; tr])
       when ls_equal eq ps_equ && t_equal tr t_bool_true
            && List.mem l renv.lv
            && List.mem g renv.lv
            && List.for_all
                 (fun t -> match t.t_node with
                           | Tvar vy -> List.mem vy renv.lv
                           | _ -> false)
                 vyl
    ->
     if debug then Format.printf "case context@.";
     let renv = add_to_maps renv vyl in
     invert_ctx_interp renv interp t l g
  | _ -> if debug then Format.printf "no reify_term match@.";
         if debug then Format.printf "lv = [%a]@."
                                     (Pp.print_list Pp.space Pretty.print_vs)
                                     renv.lv;
         raise NoReification

let build_vars_map renv prev =
  if debug then Format.printf "building vars map@.";
  let subst, prev = Mvs.fold
                (fun vy ty_vars (subst, prev) ->
                  if debug then Format.printf "creating var map %a@."
                                              Pretty.print_vs vy;
                  let ly = create_fsymbol (Ident.id_fresh vy.vs_name.id_string)
                                          [] ty_vars in
                  let y = t_app ly [] (Some ty_vars) in
                  let d = create_param_decl ly in
                  let prev = Task.add_decl prev d in
                  Mvs.add vy y subst, prev)
                renv.var_maps (renv.subst, prev) in
  let prev = Mvs.fold
               (fun vy _ prev ->
                 if debug then Format.printf "checking %a@." Pretty.print_vs vy;
                 let vs = Mty.find vy.vs_ty renv.ty_to_map in
                 if vs_equal vy vs then prev
                 else begin
                   if debug
                   then Format.printf "aliasing %a and %a@."
                                      Pretty.print_vs vy Pretty.print_vs vs;
                   let y = Mvs.find vy subst in
                   let z = Mvs.find vs subst in
                   let et = t_equ y z in
                   let pr = create_prsymbol (Ident.id_fresh "map_alias") in
                   let d = create_prop_decl Paxiom pr et in
                   Task.add_decl prev d end)
               renv.var_maps prev in
  if not (List.for_all (fun v -> Mvs.mem v subst) renv.lv)
  then (if debug
        then Format.printf "vars not matched: %a@."
                           (Pp.print_list Pp.space Pretty.print_vs)
                           (List.filter (fun v -> not (Mvs.mem v subst)) renv.lv);
        raise Exit);
  if debug then Format.printf "all vars matched@.";
  let prev = Mterm.fold
               (fun t (vy,i) prev ->
                 let y = Mvs.find vy subst in
                 let et = t_equ
                            (t_app fs_func_app [y; t_nat_const i]
                                   t.t_ty)
                            t in
                 if debug then Format.printf "%a %d = %a@."
                                             Pretty.print_vs vy i Pretty.print_term t;
                 let pr = create_prsymbol (Ident.id_fresh "y_val") in
                 let d = create_prop_decl Paxiom pr et in
                 Task.add_decl prev d)
               renv.store prev in
  subst, prev

let build_goals prev subst lp g rt =
  if debug then Format.printf "building goals@.";
  let inst_rt = t_subst subst rt in
  if debug then Format.printf "reified goal instantiated@.";
  let inst_lp = List.map (t_subst subst) lp in
  if debug then Format.printf "premises instantiated@.";
  let hr = create_prsymbol (id_fresh "HR") in
  let d_r = create_prop_decl Paxiom hr inst_rt in
  let pr = create_prsymbol
             (id_fresh "GR"
                       ~label:(Slab.singleton expl_reification_check)) in
  let d = create_prop_decl Pgoal pr g in
  let task_r = Task.add_decl (Task.add_decl prev d_r) d in
  if debug then Format.printf "building cut indication rt %a g %a@."
                              Pretty.print_term rt Pretty.print_term g;
  let ltask_r =
    try let ci =
          match (rt.t_node, g.t_node) with
          | (Tapp(eq, rh::rl),
             Tapp(eq', h::l))
               when ls_equal eq eq' ->
             List.fold_left2 (fun ci st rst -> t_and ci (t_equ (t_subst subst rst) st))
                             (t_equ (t_subst subst rh) h)
                             l rl
          | _,_ when g.t_ty <> None -> t_equ (t_subst subst rt) g
          | _ -> raise Exit in
        (* todo on context interp, revert post
           and compute_specified interp functions*)
        if debug then Format.printf "cut ok@.";
        Trans.apply (Cut.cut ci (Some "interp")) task_r
    with _ -> if debug then Format.printf "no cut found@."; [task_r] in
  let lt = List.map (fun ng -> Task.add_decl prev
                       (create_prop_decl Pgoal (create_prsymbol (id_fresh "G")) ng))
                    inst_lp in
  if debug then Format.printf "done@.";
  ltask_r@lt

let reflection_by_lemma pr env : Task.task Trans.tlist = Trans.store (fun task ->
  let kn = task_known task in
  let g, prev = Task.task_separate_goal task in
  let g = Apply.term_decl g in
  try
    if debug then Format.printf "start@.";
    let d = Apply.find_hypothesis pr.pr_name prev in
    if d = None then raise Exit;
    let d = Opt.get d in
    let l = Apply.term_decl d in
    let (lp, lv, rt) = Apply.intros l in
    let renv = reify_term (init_renv kn lv env prev) g rt in
    let subst, prev = build_vars_map renv prev in
    build_goals prev subst lp g rt
  with NoReification | Exit -> [task])

open Mltree
open Expr
open Ity

exception CannotReduce

type value =
  | Vconstr of rsymbol * field list
  | Vint of BigInt.t
  | Vbool of bool
  | Vvoid
  | Varray of value array
  | Vmatrix of value array array
  | Vref of value ref

and field = Fimmutable of value | Fmutable of value ref

open Format

let rec print_value fmt = function
  | Vvoid -> fprintf fmt "Vvoid"
  | Vbool b -> fprintf fmt "Vbool %b" b
  | Vint i -> fprintf fmt "Vint %a" Number.print_constant (Number.const_of_big_int i)
  | Vconstr (rs, lf) -> fprintf fmt "Vconstr(%a, %a)"
                                Expr.print_rs rs
                                (Pp.print_list Pp.space print_field) lf
  | Varray a -> fprintf fmt "Varray [|%a|]"
                        (Pp.print_list Pp.space print_value) (Array.to_list a)
  | Vmatrix m -> fprintf fmt "Vmatrix %a" print_matrix m
  | Vref r -> fprintf fmt "Vref %a" print_value !r

and print_field fmt = function
  | Fimmutable v -> fprintf fmt "Fimmutable %a" print_value v
  | Fmutable vr -> fprintf fmt "Fmutable %a" print_value !vr
and print_matrix fmt m =
  Array.iter (fun a -> fprintf fmt "[|%a|]\n"
                               (Pp.print_list Pp.space print_value)
                               (Array.to_list a)) m

let field_get f = match f with
  | Fimmutable v -> v
  | Fmutable v -> !v

open Stdlib

let find_module_path env mm path m =
  if debug
  then Format.printf "find_module_path path %a m %s@."
                     (Pp.print_list Pp.space Pp.string) path m;
  match path with
  | [] -> Mstr.find m mm
  | path -> let mm = Env.read_library Pmodule.mlw_language env path in
            Mstr.find m mm

let find_module_id env mm id =
  let (path, m, _) = Pmodule.restore_path id in find_module_path env mm path m

let translate_module =
  let memo = Ident.Hid.create 16 in
  fun m ->
    let name = m.Pmodule.mod_theory.Theory.th_name in
    try Ident.Hid.find memo name with Not_found ->
      let pm = Compile.Translate.module_ m in
      let pm = Compile.Transform.module_ pm in
      Ident.Hid.add memo name pm;
      pm

exception Constructor
exception Field

let get_decl env mm rs =
  let open Pdecl in
  if debug then Format.printf "get_decl@.";
  let id = rs.rs_name in
  if debug then Format.printf "looking for rs %s@." id.id_string;
  let pm = find_module_id env mm id in
  if debug then Format.printf "pmodule %s@."
                              (pm.Pmodule.mod_theory.Theory.th_name.id_string);
  let tm = translate_module pm in
  if Mid.mem id tm.mod_known
  then Mid.find id tm.mod_known
  else
    let pd = Mid.find id tm.mod_from.from_km in
    match pd.pd_node with
    | PDtype l ->
       let rec aux = function
         | [] -> raise Not_found
         | d::t -> if List.mem rs d.itd_constructors then raise Constructor
                   else if List.mem rs d.itd_fields then raise Field
                   else aux t
       in
       aux l
    | _ -> raise Not_found

let builtin_progs = Hrs.create 17

let eval_true _ _ = Vbool true
let eval_false _ _ = Vbool false

let eval_int_op op _ l =
  match l with
  | [Vint i1; Vint i2] ->
     (try Vint (op i1 i2) with Division_by_zero -> raise CannotReduce)
  | _ -> raise CannotReduce

let eval_int_uop uop _ l =
  match l with
  | [Vint i] -> Vint (uop i)
  | _ -> raise CannotReduce

let eval_int_rel r _ l =
  match l with
  | [Vint i1; Vint i2] ->
     Vbool (r i1 i2)
  | _ -> raise CannotReduce

let builtin_array_type _kn _its = ()

let exec_array_make _ args =
  match args with
    | [Vint n;def] ->
      begin
        try
          let n = BigInt.to_int n in
          let v = Varray(Array.make n def) in
          v
        with _ -> raise CannotReduce
      end
    | _ ->
      raise CannotReduce

let exec_array_copy _ args =
  match args with
    | [Varray a] -> Varray(Array.copy a)
    | _ ->
      raise CannotReduce

let exec_array_get _ args =
  match args with
    | [Varray a;Vint i] ->
      begin
        try
          a.(BigInt.to_int i)
        with _ -> raise CannotReduce
      end
    | _ -> raise CannotReduce

let exec_array_length _ args =
  match args with
    | [Varray a] -> Vint (BigInt.of_int (Array.length a))
    | _ -> raise CannotReduce

let exec_array_set _ args =
  match args with
    | [Varray a;Vint i;v] ->
      begin
        try
          a.(BigInt.to_int i) <- v;
          Vvoid
        with _ -> raise CannotReduce
      end
    | _ -> raise CannotReduce

let builtin_matrix_type _kn _its = ()

let exec_matrix_make _ args =
  match args with
  | [Vint r; Vint c; def] ->
     begin
       try
         let r = BigInt.to_int r in
         let c = BigInt.to_int c in
         Vmatrix(Array.make_matrix r c def)
       with _ -> raise CannotReduce
     end
  | _ -> raise CannotReduce

let exec_matrix_get _ args =
  match args with
  | [Vmatrix m; Vint i; Vint j] ->
     begin
       try
         m.(BigInt.to_int i).(BigInt.to_int j)
       with _ -> raise CannotReduce
     end
  | _ -> raise CannotReduce

let exec_matrix_set _ args =
  match args with
  | [Vmatrix m; Vint i; Vint j; v] ->
     begin
       try
         m.(BigInt.to_int i).(BigInt.to_int j) <- v;
         Vvoid
       with _ -> raise CannotReduce
     end
  | _ -> raise CannotReduce

let exec_matrix_rows _ args =
  match args with
  | [Vmatrix m] -> Vint (BigInt.of_int (Array.length m))
  | _ -> raise CannotReduce

(* FIXME fails if rows=0 *)
let exec_matrix_cols _ args =
  match args with
  | [Vmatrix m] ->
     begin
       try Vint (BigInt.of_int (Array.length m.(0)))
       with _ -> raise CannotReduce
     end
  | _ -> raise CannotReduce

let exec_matrix_copy _ args =
  match args with
  | [Vmatrix m] ->
     let a = Array.copy m in
     for i = 0 to (Array.length m - 1) do
       a.(i) <- Array.copy m.(i)
     done;
     Vmatrix a
  | _ -> raise CannotReduce

let exec_ref_make _ args =
  match args with
  | [v] ->
     Vref (ref v)
  | _ -> raise CannotReduce

let exec_ref_get _ args =
  match args with
  | [Vref r] -> !r
  | _ -> raise CannotReduce

let exec_ref_set _ args =
  match args with
  | [Vref r; v] ->
     r := v;
     Vvoid
  | _ -> raise CannotReduce

let built_in_modules =
  [
    ["bool"],"Bool", [],
    [ "True", eval_true ;
      "False", eval_false ;
    ] ;
    ["int"],"Int", [],
    [ "infix +", eval_int_op BigInt.add;
      (* defined as x+(-y)
         "infix -", eval_int_op BigInt.sub; *)
      "infix *", eval_int_op BigInt.mul;
      "prefix -", eval_int_uop BigInt.minus;
      "infix =", eval_int_rel BigInt.eq;
      "infix <", eval_int_rel BigInt.lt;
      "infix <=", eval_int_rel BigInt.le;
      "infix >", eval_int_rel BigInt.gt;
      "infix >=", eval_int_rel BigInt.ge;
    ] ;
    ["int"],"MinMax", [],
    [ "min", eval_int_op BigInt.min;
      "max", eval_int_op BigInt.max;
    ] ;
    ["int"],"ComputerDivision", [],
    [ "div", eval_int_op BigInt.computer_div;
      "mod", eval_int_op BigInt.computer_mod;
    ] ;
    ["int"],"EuclideanDivision", [],
    [ "div", eval_int_op BigInt.euclidean_div;
      "mod", eval_int_op BigInt.euclidean_mod;
    ] ;
    ["array"],"Array",
    ["array", builtin_array_type],
    ["make", exec_array_make ;
     "mixfix []", exec_array_get ;
     "length", exec_array_length ;
     "mixfix []<-", exec_array_set ;
     "copy", exec_array_copy ;
    ] ;
    ["matrix"],"Matrix",
    ["matrix", builtin_matrix_type],
    ["make", exec_matrix_make ;
     "get", exec_matrix_get ;
     "rows", exec_matrix_rows ;
     "columns", exec_matrix_cols ;
     "set", exec_matrix_set ;
     "copy", exec_matrix_copy ;
    ] ;
    ["ref"],"Ref",
    [], (* ? *)
    ["ref", exec_ref_make ;
     "prefix !", exec_ref_get;
     "infix :=", exec_ref_set;
    ] ;
  ]

let add_builtin_mo env (l,n,t,d) =
  let mo = Pmodule.read_module env l n in
  let exp = mo.Pmodule.mod_export in
  let kn = mo.Pmodule.mod_known in
  List.iter
    (fun (id,r) ->
      let its = Pmodule.ns_find_its exp [id] in
      r kn its)
    t;
  List.iter
    (fun (id,f) ->
      let ps = Pmodule.ns_find_rs exp [id] in
      Hrs.add builtin_progs ps f)
    d

let get_builtin_progs lib =
  List.iter (add_builtin_mo lib) built_in_modules

type info = {
    env : Env.env;
    mm  : Pmodule.pmodule Mstr.t;
    vars: value Mid.t;
    recs: rsymbol Mrs.t;
    funs: decl Mrs.t;
  }

let print_id fmt id = fprintf fmt "%s" id.id_string

let get pv info : value =  Mid.find pv.pv_vs.vs_name info.vars

let add_id id v info = {info with vars = Mid.add id v info.vars}
let add_vs vs = add_id vs.vs_name
let add_pv pv = add_vs pv.pv_vs

let add_fundecl rs decl info =
  if debug then Format.printf "adding decl for %s@." rs.rs_name.id_string;
  { info with funs = Mrs.add rs decl info.funs }

exception NoMatch

let rec matching info v pat =
  match pat with
  | Pwild -> info
  | Pvar vs -> add_vs vs v info
  | Ptuple pl ->
     begin match v with
     | Vconstr (rs, l) ->
        assert (is_rs_tuple rs);
        List.fold_left2 matching info (List.map field_get l) pl
     | _ -> assert false
     end
  | Por (p1, p2) ->
     begin try matching info v p1 with NoMatch -> matching info v p2 end
  | Pas (p, vs) -> add_vs vs v (matching info v p)
  | Papp (ls, pl) ->
     match v with
     | Vconstr ({rs_logic = RLls ls2}, l) ->
        if ls_equal ls ls2 then
          List.fold_left2 matching info (List.map field_get l) pl
        else if ls2.ls_constr > 0 then raise NoMatch
        else assert false
     | Vbool b ->
        let ls2 = if b then fs_bool_true else fs_bool_false in
        if ls_equal ls ls2 then info else raise NoMatch
     | _ -> raise CannotReduce

let rec interp_expr info (e:Mltree.expr) : value =
  Mltree.(match e.e_node with
  | Econst nc -> Vint (Number.compute_int_constant nc)
  | Evar pv ->
     (try get pv info
      with Not_found ->
           if debug
           then Format.printf "var %a not found@." print_pv pv;
           raise CannotReduce)
  | Eapp (rs, le) -> begin
      if debug then Format.printf "Eapp %a@." Expr.print_rs rs;
      let eval_call info vl e =
        if debug then Format.printf "eval params@.";
        let info' =
          List.fold_left2
            (fun info e (id, _ty, ig) ->
              assert (not ig);
              let v = interp_expr info e in
              if debug
              then Format.printf "arg %a : %a@." print_id id print_value v;
              add_id id v info)
            info le vl in
        interp_expr info' e in
      if debug then Format.printf "eval call@.";
      let res = try begin
        let rs = if Mrs.mem rs info.recs then Mrs.find rs info.recs else rs in
        if Hrs.mem builtin_progs rs
        then
          (if debug then Format.printf "%a is builtin@." Expr.print_rs rs;
          let f = Hrs.find builtin_progs rs in
          f rs (List.map (interp_expr info) le))
        else begin
          let decl = try Mrs.find rs info.funs
                     with Not_found -> get_decl info.env info.mm rs in
          if debug then Format.printf "decl found@.";
          match decl with
          | Dlet (Lsym (_rs, _ty, vl, e)) ->
             eval_call info vl e
          | Dlet(Lrec([{rec_args = vl; rec_exp = e;
                        rec_sym = rs; rec_rsym = rrs; rec_res=_ty}])) ->
             eval_call { info with recs = Mrs.add rrs rs info.recs } vl e
          | Dlet (Lrec _) ->
             if debug
             then Format.printf "unhandled mutually recursive functions@.";
             raise CannotReduce
          | Dlet (Lvar _) ->
             if debug then Format.printf "Lvar@."; raise CannotReduce
          | Dlet (Lany _) ->
             if debug then Format.printf "Lany@."; raise CannotReduce
          | _ -> if debug then Format.printf "not a let decl@.";
                 raise CannotReduce
          end
                  end
      with
      | Constructor ->
         if debug then Format.printf "constructor@.";
         let field_of_expr pv e =
           let is_mutable = match pv.pv_ity.ity_node with
             | Ityreg _ -> true
             | _ -> false
           in
           let v = interp_expr info e in
           if is_mutable then Fmutable (ref v) else Fimmutable v
         in
         Vconstr(rs, List.map2 field_of_expr rs.rs_cty.cty_args le)
      | Field ->
         if debug then Format.printf "field@.";
         (* TODO keep field info when applying constructors, use here ?*)
         raise CannotReduce
      | Not_found ->
         if debug
         then Format.printf "decl not found@.";
         raise CannotReduce
      in
      if debug then Format.printf "result: %a@." print_value res;
      res
    end
  | Efun _ -> if debug then Format.printf "Efun@."; raise CannotReduce
  | Elet (Lvar(pv, e), ein) ->
     let v = interp_expr info e in
     interp_expr (add_pv pv v info) ein
  | Eif (c, th, el) ->
     begin match interp_expr info c with
     | Vbool true -> interp_expr info th
     | Vbool false -> interp_expr info el
     | _ -> raise CannotReduce
     end
  | Eassign l ->
     List.iter
       (fun (pvs, rs, v) ->
         let fld = fd_of_rs rs in
         let value = get v info in
         match get pvs info with
         | Vconstr(c, args) ->
            let rec aux cargs args =
              match cargs, args with
              | pv :: pvl, v :: vl ->
                 if pv_equal pv fld then
                   match v with
                   | Fmutable r -> r := value
                   | Fimmutable _ -> assert false
                 else
                   aux pvl vl
              | _ -> raise CannotReduce
            in
            aux c.rs_cty.cty_args args
         | _ -> assert false)
       l;
     Vvoid
  | Ematch (e, l) ->
     if debug then Format.printf "Ematch@.";
     let v = interp_expr info e in
     if debug then Format.printf "value %a@." print_value v;
     let rec aux = function
       | [] -> assert false
       | (p,e)::tl ->
          try
            let info' = matching info v p in
            interp_expr info' e
          with NoMatch -> aux tl
     in
     aux l
  | Eblock l ->
     List.fold_left
       (fun _ e -> interp_expr info e) (*ignore all but last result*)
       Vvoid l
  | Eignore e -> ignore (interp_expr info e); Vvoid
  | Ewhile (c, b) ->
     if debug then Format.printf "while@.";
     begin match interp_expr info c with
     | Vbool true ->
        ignore (interp_expr info b);
        interp_expr info e
     | Vbool false -> Vvoid
     | _ -> raise CannotReduce end
  | Efor (x, pv1, dir, pv2, e) ->
     if debug then Format.printf "for@.";
     begin match (get pv1 info, get pv2 info) with
     | (Vint i1, Vint i2) ->
        if dir = To
        then
          for i = BigInt.to_int i1 to BigInt.to_int i2 do
            ignore (interp_expr (add_pv x (Vint (BigInt.of_int i)) info) e)
          done
        else
          for i = BigInt.to_int i1 downto BigInt.to_int i2 do
            ignore (interp_expr (add_pv x (Vint (BigInt.of_int i)) info) e)
          done;
        Vvoid
     | _ -> if debug then Format.printf "Non-integer for bounds@.";
            raise CannotReduce
     end
  | Elet (Lany _,_) -> if debug then Format.printf "unhandled Lany@.";
                       raise CannotReduce
  | Elet ((Lsym(rs,_,_,_) as ld), e) ->
     interp_expr (add_fundecl rs (Dlet ld) info) e
  | Elet ((Lrec rdl as ld), e) ->
     let info = List.fold_left
                  (fun info rd -> add_fundecl rd.rec_sym (Dlet ld) info)
                  info rdl in
     interp_expr info e
  | Eraise (xs,_)  ->
     if debug then Format.printf "Eraise %s@." xs.xs_name.id_string;
     raise CannotReduce
  | Eexn  _ -> if debug then Format.printf "Eexn@.";
                         raise CannotReduce
  | Eabsurd -> if debug then Format.printf "Eabsurd@.";
               raise CannotReduce
  | Ehole -> if debug then Format.printf "Ehole@.";
             raise CannotReduce
  | Etry _-> if debug then Format.printf "Etry@."; raise CannotReduce)

let eval_fun decl info = match decl with
  | Dlet (Lsym (_rs, _, _vl, expr)) ->
     interp_expr info expr
  | _ -> raise CannotReduce

let rec value_of_term t =
  match t.t_node with
  | Ttrue -> Vbool true
  | Tfalse -> Vbool false
  | Term.Tapp (ls, lp) when ls.ls_constr > 0 ->
     Vconstr ((restore_rs ls),
              (List.map (fun t -> Fimmutable (value_of_term t)) lp))
  | Tnot t -> begin match value_of_term t with
              | Vbool b -> Vbool (not b)
              | _ -> raise CannotReduce end
  (* TODO Tbinop maybe *)
  | Tconst (Number.ConstInt ic) -> Vint (Number.compute_int_constant ic)
  | _ -> raise CannotReduce

let rec term_of_value = function
  | Vbool true -> t_bool_true
  | Vbool false -> t_bool_false
  | Vint i -> t_bigint_const i
  | Vconstr (rs, lf) ->
     t_app (ls_of_rs rs) (List.map (fun f -> term_of_value (field_get f)) lf)
           (ls_of_rs rs).ls_value
  | Vvoid -> t_void
  | Vref _ -> raise CannotReduce (* TODO ? *)
  | Varray _ -> raise CannotReduce
  | Vmatrix _ -> raise CannotReduce

(*exception FunctionNotFound*)

let reflection_by_function s env = Trans.store (fun task ->
  if debug then Format.printf "reflection_f start@.";
  let kn = task_known task in
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
          else (if debug then Format.printf "Name conflict %s@." s;
                raise Exit)
        with Not_found -> o)
      ths None in
  let (_pmod, rs) = if o = None
                   then (if debug then Format.printf "Symbol %s not found@." s;
                         raise Exit)
                   else Opt.get o in
  (*let (_, ms, _) = Pmodule.restore_path rs.rs_name in*) (*FIXME remove or adapt*)
  let lpost = List.map open_post rs.rs_cty.cty_post in
  if List.exists (fun pv -> pv.pv_ghost) rs.rs_cty.cty_args
  then (if debug then Format.printf "ghost parameter@.";
        raise Exit);
  if debug then Format.printf "building module map@.";
  let mm = Mid.fold
             (fun id th acc ->
               try
                 let pm = Pmodule.restore_module th in
                 Mstr.add id.id_string pm acc
               with Not_found -> acc)
             ths Mstr.empty in
  (*let mm = Mstr.singleton ms pmod in*)
  if debug then Format.printf "module map built@.";
  get_builtin_progs env;
  let decl = get_decl env mm rs in
  if debug then Format.printf "initial decl found@.";
  let args = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
  let rec reify_post = function
    | [] -> if debug then Format.printf "no postcondition reifies@.";
            raise NoReification
    | (vres, p)::t -> begin
        try
          if debug then Format.printf "new post@.";
          if debug
          then Format.printf "post: %a, %a@."
                             Pretty.print_vs vres Pretty.print_term p;
          let (lp, lv, rt) = Apply.intros p in
          let lv = lv @ args in
          let renv = reify_term (init_renv kn lv env prev) g rt in
          (*ignore (build_vars_map renv prev);
          Mvs.iter (fun v t -> if debug then Format.printf "%a %a@."
                                           Pretty.print_vs v
                                           Pretty.print_term t)
                   renv.subst;
          assert false;*)   (*stop at reification and dump context*)
          if debug then Format.printf "computing args@.";
          let vars =
            List.fold_left
              (fun vars (vs, t) ->
                if List.mem vs args
                then begin
                    if debug then Format.printf "value of term %a for arg %a@."
                                                Pretty.print_term t
                                                Pretty.print_vs vs;
                    Mid.add vs.vs_name (value_of_term t) vars end
                else vars)
              Mid.empty
              (Mvs.bindings renv.subst) in
          let info = { env = env;
                       mm = mm;
                       funs = Mrs.empty;
                       recs = Mrs.empty;
                       vars = vars
                       } in
          if debug then Format.printf "eval_fun@.";
          let res = term_of_value (eval_fun decl info) in
          if debug then Format.printf "res %a@." Pretty.print_term res;
          let rinfo = {renv with subst = Mvs.add vres res renv.subst} in
          rinfo, lp, lv, rt
        with NoReification -> reify_post t
      end
  in
  let rinfo, lp, _lv, rt = reify_post lpost in
  let lp = (rs.rs_cty.cty_pre)@lp in
  let subst, prev = build_vars_map rinfo prev in
  build_goals prev subst lp g rt)

let () = wrap_and_register
           ~desc:"reflection_l <prop> attempts to prove the goal by reflection using the lemma prop"
           "reflection_l"
           (Tprsymbol Tenvtrans_l) reflection_by_lemma

let () = wrap_and_register
           ~desc:"reflection_f <f> attempts to prove the goal by reflection using the contract of the program function f"
           "reflection_f"
           (Tstring Tenvtrans_l) reflection_by_function

(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
