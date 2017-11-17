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
                   store: int Mterm.t;
                   fr: int;
                   subst: term Mvs.t;
                   lv: Svs.t;
                   vy: vsymbol option;
                   ty_val: ty option;
                 }

let init_renv kn lv = { kn=kn;
                        store = Mterm.empty;
                        fr = 0;
                        subst = Mvs.empty;
                        lv = lv;
                        vy = None;
                        ty_val = None;
                      }

let rec reify_term renv t rt =
  let rec invert_pat vl (env, fr) interp (p,f) t =
    if debug
    then Format.printf
           "invert_pat p %a f %a t %a@."
           Pretty.print_pat p Pretty.print_term f Pretty.print_term t;
    match p.pat_node, f.t_node, t.t_node with
    | Pwild, _, _ -> raise NoReification
    | Papp (cs, [{pat_node = Pvar v1}]),
      Tapp (ffa,[{t_node = Tvar vy}; {t_node = Tvar v2}]),
      Tvar _
      | Papp (cs, [{pat_node = Pvar v1}]),
        Tapp (ffa,[{t_node = Tvar vy}; {t_node = Tvar v2}]),
        Tapp(_, [])
         when ty_equal v1.vs_ty ty_int
              && Svs.mem v1 p.pat_vars
              && vs_equal v1 v2
              && ls_equal ffa fs_func_app
              && List.exists (fun vs -> vs_equal vs vy) vl (*FIXME*)
      ->
       if debug then Format.printf "case var@.";
       let rty = cs.ls_value in
       if Mterm.mem t env
       then
         begin
           if debug then Format.printf "%a exists@." Pretty.print_term t;
           (env, fr, t_app cs [t_nat_const (Mterm.find t env)] rty)
         end
       else
         begin
           if debug then Format.printf "%a is new@." Pretty.print_term t;
           let env = Mterm.add t fr env in
           (env, fr+1, t_app cs [t_nat_const fr] rty)
         end
    | Papp (cs, pl), Tapp(ls1, la1), Tapp(ls2, la2) when ls_equal ls1 ls2
      ->
       if debug then Format.printf "case app@.";
       (* same head symbol, match parameters *)
       let env, fr, rl =
         fold_left3
           (fun (env, fr, acc) p f t ->
             let env, fr, nt = invert_pat vl (env, fr) interp (p, f) t in
             if debug
             then Format.printf "param %a matched@." Pretty.print_term t;
             (env, fr, nt::acc))
           (env, fr, []) pl la1 la2 in
       if debug then Format.printf "building app %a of type %a with args %a@."
                                   Pretty.print_ls cs
                                   Pretty.print_ty (Opt.get cs.ls_value)
                                   (Pp.print_list Pp.comma Pretty.print_term)
                                   (List.rev rl);
       let t = t_app cs (List.rev rl) cs.ls_value in
       if debug then Format.printf "app ok@.";
       env, fr, t
    | Papp _, Tapp (ls1, _), Tapp(ls2, _) ->
       if debug then Format.printf "head symbol mismatch %a %a@."
                                   Pretty.print_ls ls1 Pretty.print_ls ls2;
       raise NoReification
    | Por (p1, p2), _, _ ->
       if debug then Format.printf "case or@.";
       begin try invert_pat vl (env, fr) interp (p1, f) t
             with NoReification -> invert_pat vl (env, fr) interp (p2, f) t
       end
    | Pvar _, Tvar _, Tvar _ | Pvar _, Tvar _, Tapp (_, [])
      | Pvar _, Tvar _, Tconst _
      -> if debug then Format.printf "case vars@.";
         (env, fr, t)
    | Pvar _, Tapp (ls, _la), _ when ls_equal ls interp
      -> if debug then Format.printf "case interp@.";
         invert_interp (env, fr) ls t
    (*| Papp (cs, pl), Tapp (ls1, la1), _ when Sls.mem ls1 !reify_invert
    -> (* Cst c -> morph c <- 42 ? *) *)
    | _ -> raise NoReification
  and invert_interp (env, fr) ls (t:term) = (*la ?*)
    let ld = Opt.get (find_logic_definition renv.kn ls) in
    let vl, f = open_ls_defn ld in
    (*assert (oty_equal f.t_ty t.t_ty);*)
    if debug then Format.printf "invert_interp ls %a t %a@."
                                Pretty.print_ls ls Pretty.print_term t;
    match f.t_node, t.t_node with
    | Tcase (x, bl), _ ->
       (*FIXME*)
       assert (List.length vl = 2);
       (match x.t_node with
        | Tvar v when vs_equal v (List.hd vl) -> ()
        | _ -> assert false);
       if debug then Format.printf "case match@.";
       let rec aux = function
         | [] -> raise NoReification
         | tb::l ->
            try invert_pat vl (env, fr) ls (t_open_branch tb) t
            with NoReification ->
                 if debug then Format.printf "match failed@."; aux l in
       aux bl
    | _ -> raise NoReification in
  if debug then Format.printf "reify_term %a@." Pretty.print_term t;
  if not (oty_equal t.t_ty rt.t_ty)
  then (if debug then Format.printf "reification type mismatch@.";
        raise NoReification);
  match t.t_node, rt.t_node with
  | _, Tapp(interp, [{t_node = Tvar vx}; {t_node = Tvar vy'} ])
       when Svs.mem vx renv.lv && Svs.mem vy' renv.lv  ->
     if debug then Format.printf "case interp@.";
     if renv.vy <> None && not (vs_equal (Opt.get renv.vy) vy')
     then (if debug then Format.printf "y map conflict@.";
           raise NoReification);
     let store, fr, x = invert_interp (renv.store, renv.fr) interp t in
     let renv =  { renv with store = store; fr = fr; subst = Mvs.add vx x renv.subst } in
     if renv.vy = None
     then begin
       assert (renv.ty_val = None);
       let ty_val = match interp.ls_args, interp.ls_value with
         | [ _ty_target; ty_vars ], Some ty_val
              when ty_equal ty_vars (ty_func ty_int ty_val)
           -> ty_val
         | _ -> raise NoReification in
       {renv with vy = Some vy'; ty_val = Some ty_val } end
     else renv
  | Tapp(eq, [t1; t2]), Tapp (eq', [rt1; rt2])
       when ls_equal eq ps_equ && ls_equal eq' ps_equ ->
     reify_term (reify_term renv t1 rt1) t2 rt2
  | _ -> raise NoReification

let build_vars_map renv prev =
    if debug then Format.printf "building vars map@.";
    let ty_val = Opt.get renv.ty_val in
    let ty_vars = ty_func ty_int ty_val in
    let ly = create_fsymbol (Ident.id_fresh "y") [] ty_vars in
    let y = t_app ly [] (Some ty_vars) in
    let vy = Opt.get renv.vy in
    let subst = Mvs.add vy y renv.subst in
    if not (Svs.for_all (fun v -> Mvs.mem v subst) renv.lv)
    then (if debug
          then Format.printf "some vars not matched, todo use context";
          raise Exit);
    let d = create_param_decl ly in
    let prev = Task.add_decl prev d in
    let prev = Mterm.fold
                 (fun t i prev ->
                   let et = t_equ
                              (t_app fs_func_app [y; t_nat_const i]
                                     (Some ty_val))
                              t in
                   if debug then Format.printf "eq_term ok@.";
                   let pr = create_prsymbol (Ident.id_fresh "y_val") in
                   let d = create_prop_decl Paxiom pr et in
                   Task.add_decl prev d)
                 renv.store prev in
    subst, prev

let build_goals prev subst lp g rt =
  let inst_rt = t_subst subst rt in
  let inst_lp = List.map (t_subst subst) lp in
  let d_r = create_prop_decl Paxiom
                             (create_prsymbol (id_fresh "HR")) inst_rt in
  let pr = create_prsymbol
             (id_fresh "GR"
                       ~label:(Slab.singleton expl_reification_check)) in
  let d = create_prop_decl Pgoal pr g in
  let task_r = Task.add_decl (Task.add_decl prev d_r) d in
  if debug then Format.printf "building cut indication@.";
  let ci =
    match (rt.t_node, g.t_node) with
    | (Tapp(eq, rh::rl),
       Tapp(eq', h::l))
         when ls_equal eq eq' ->
       List.fold_left2 (fun ci st rst -> t_and ci (t_equ (t_subst subst rst) st))
                       (t_equ (t_subst subst rh) h)
                       l rl
    | _,_ when g.t_ty <> None -> t_equ (t_subst subst rt) g
    | _ -> raise Exit in
  if debug then Format.printf "building tasks@.";
  let ltask_r = Trans.apply (Cut.cut ci (Some "interp")) task_r in
  if debug then Format.printf "cut ok@.";
  let lt = List.map (fun ng -> Task.add_decl prev
                       (create_prop_decl Pgoal (create_prsymbol (id_fresh "G")) ng))
                    inst_lp in
  if debug then Format.printf "done@.";
  ltask_r@lt

let reflection_by_lemma pr : Task.task Trans.tlist = Trans.store (fun task ->
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
    let renv = reify_term (init_renv kn lv) g rt in
    let subst, prev = build_vars_map renv prev in
    if debug then Format.printf "building goals@.";
    build_goals prev subst lp g rt
  with NoReification | Exit -> [task])


open Mltree
open Expr
open Ity

exception CannotReduce

type value =
  | Vconstr of rsymbol * field list
  | Vint of Number.integer_constant
  | Vbool of bool
  | Vvoid
 (*  | Varray of value array *)

and field = Fimmutable of value | Fmutable of value ref

let field_get f = match f with
  | Fimmutable v -> v
  | Fmutable v -> !v

type env = {
    pmod: Mltree.pmodule;
    vars: value Mid.t; }

let get pv env : value =  Mid.find pv.pv_vs.vs_name env.vars

let add_id id v env = {env with vars = Mid.add id v env.vars}
let add_vs vs = add_id vs.vs_name
let add_pv pv = add_vs pv.pv_vs

exception NoMatch

let rec matching env v pat =
  match pat with
  | Pwild -> env
  | Pvar vs -> add_vs vs v env
  | Ptuple pl ->
     begin match v with
     | Vconstr (rs, l) ->
        assert (is_rs_tuple rs);
        List.fold_left2 matching env (List.map field_get l) pl
     | _ -> assert false
     end
  | Por (p1, p2) ->
     begin try matching env v p1 with NoMatch -> matching env v p2 end
  | Pas (p, vs) -> add_vs vs v (matching env v p)
  | Papp (ls, pl) ->
     match v with
     | Vconstr ({rs_logic = RLls ls2}, l) ->
        if ls_equal ls ls2 then
          List.fold_left2 matching env (List.map field_get l) pl
        else if ls2.ls_constr > 0 then raise NoMatch
        else assert false
     | Vbool b ->
        let ls2 = if b then fs_bool_true else fs_bool_false in
        if ls_equal ls ls2 then env else raise NoMatch
     | _ -> raise CannotReduce

let rec interp_expr env (e:Mltree.expr) : value =
  Mltree.(match e.e_node with
  | Econst nc -> Vint nc
  | Evar pv -> (try get pv env
                with Not_found ->
                     if debug
                     then Format.printf "var %a not found@." print_pv pv;
                     raise CannotReduce)
  | Eapp (rs, le) ->
     begin try
       let decl = Mid.find rs.rs_name env.pmod.mod_known in
       begin match decl with
       | Dlet (Lsym (_rs, _ty, vl, e)) when List.length le = List.length vl ->
          let env' =
            List.fold_left2
              (fun env e (id, _ty, ig) ->
                assert (not ig);
                let v = interp_expr env e in
                add_id id v env)
              env le vl in
          interp_expr env' e
       | _ -> raise CannotReduce
       end
       with Not_found -> raise CannotReduce
     end
  | Efun _ -> raise CannotReduce
  | Elet (Lvar(pv, e), ein) ->
     let v = interp_expr env e in
     interp_expr (add_pv pv v env) ein
  (* FIXME other let decls *)
  | Eif (c, th, el) ->
     begin match interp_expr env c with
     | Vbool true -> interp_expr env th
     | Vbool false -> interp_expr env el
     | _ -> raise CannotReduce
     end
  | Eassign l ->
     List.iter
       (fun (pvs, rs, v) ->
         let fld = fd_of_rs rs in
         let value = get v env in
         match get pvs env with
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
     let v = interp_expr env e in
     let rec aux = function
       | [] -> assert false
       | (p,e)::tl ->
          try
            let env' = matching env v p in
            interp_expr env' e
          with NoMatch -> aux tl
     in
     aux l
  | Eblock l ->
     List.fold_left
       (fun _ e -> interp_expr env e) (*ignore all but last result*)
       Vvoid l
  | Eignore e -> ignore (interp_expr env e); Vvoid
  | Ewhile (c, b) ->
     begin match interp_expr env c with
     | Vbool true ->
        ignore (interp_expr env b);
        interp_expr env e
     | Vbool false -> Vvoid
     | _ -> raise CannotReduce end
  | _ -> raise CannotReduce)

let eval_fun decl env = match decl with
  | Dlet (Lsym (_rs, _, _vl, expr)) ->
     interp_expr env expr
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
  | Tconst (Number.ConstInt ic) -> Vint ic
  | _ -> raise CannotReduce

let rec term_of_value = function
  | Vbool true -> t_true
  | Vbool false -> t_false
  | Vint ic -> t_bigint_const (Number.compute_int_constant ic)
  | Vconstr (rs, lf) ->
     t_app (ls_of_rs rs) (List.map (fun f -> term_of_value (field_get f)) lf)
           (ls_of_rs rs).ls_value
  | Vvoid -> t_void

let reflection_by_function ls : task Trans.tlist = Trans.store (fun task ->
  let kn = task_known task in
  let g, prev = Task.task_separate_goal task in
  let g = Apply.term_decl g in
  try
    let rs = restore_rs ls in
    let lpost = List.map open_post rs.rs_cty.cty_post in
    if List.exists (fun pv -> pv.pv_ghost) rs.rs_cty.cty_args
    then (if debug then Format.printf "ghost parameter@.";
          raise Exit);
    let mith = Task.used_symbols (Task.used_theories task) in
    let th = Mid.find ls.ls_name mith in
    let pmod = Pmodule.restore_module th in
    let pmod = Compile.Transform.module_ (Compile.Translate.module_ pmod) in
    let decl = Mid.find rs.rs_name pmod.mod_known in
    let args = List.map (fun pv -> pv.pv_vs) rs.rs_cty.cty_args in
    let rec reify_post = function
      | [] -> raise NoReification
      | (vres, p)::t -> begin
          try
            let (lp, lv, rt) = Apply.intros p in
            let renv = reify_term (init_renv kn lv) g rt in
            let env = { pmod = pmod;
                        vars =
                          List.fold_left
                            (fun vars (vs, t) ->
                              if List.mem vs args
                              then Mid.add vs.vs_name (value_of_term t) vars
                              else vars)
                            Mid.empty
                            (Mvs.bindings renv.subst) } in
            let res = term_of_value (eval_fun decl env) in
            let renv = {renv with subst = Mvs.add vres res renv.subst} in
            renv, lp, lv, rt
          with NoReification -> reify_post t
        end
    in
    let renv, lp, _lv, rt = reify_post lpost in
    let lp = (rs.rs_cty.cty_pre)@lp in
    let subst, prev = build_vars_map renv prev in
    build_goals prev subst lp g rt
  with NoReification | CannotReduce -> [task])

let () = wrap_and_register
           ~desc:"reflection_l <prop> attempts to prove the goal by reflection using the lemma prop"
           "reflection_l"
           (Tprsymbol Ttrans_l) reflection_by_lemma

let () = wrap_and_register
           ~desc:"reflection_f <f> attempts to prove the goal by reflection using the contract of the function f"
           "reflection_f"
           (Tlsymbol Ttrans_l) reflection_by_function

(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
