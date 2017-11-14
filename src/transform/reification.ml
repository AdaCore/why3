open Term
open Ty
open Decl
open Ident
open Args_wrapper

(* target: t = V int | ...
   interp: t -> (int -> 'a) -> 'a *)


let rec fold_left3 f accu l1 l2 l3 =
  match (l1, l2, l3) with
  | a1::l1, a2::l2, a3::l3 -> fold_left3 f (f accu a1 a2 a3) l1 l2 l3
  | [], [], [] -> accu
  | _ -> raise (Invalid_argument "fold_left3")


exception Exit

let debug = true


let expl_reification_check = Ident.create_label "expl:reification check"


let reflection_by_lemma pr : Task.task Trans.tlist = Trans.store (fun task ->
  let open Task in
  let kn = task_known task in
  let rec invert_pat vl (env, fr) interp (p,f) t =
    if debug
    then Format.printf "invert_pat p %a f %a t %a@."
                       Pretty.print_pat p Pretty.print_term f Pretty.print_term t;
    match p.pat_node, f.t_node, t.t_node with
    | Pwild, _, _ -> raise Exit
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
                                   (List.rev rl)
       ;
         let t = t_app cs (List.rev rl) cs.ls_value in
         if debug then Format.printf "app ok@.";
         env, fr, t
    | Papp _, Tapp (ls1, _), Tapp(ls2, _) ->
       if debug then Format.printf "head symbol mismatch %a %a@."
                                   Pretty.print_ls ls1 Pretty.print_ls ls2;
       raise Exit
    | Por (p1, p2), _, _ ->
       if debug then Format.printf "case or@.";
       begin try invert_pat vl (env, fr) interp (p1, f) t
             with Exit -> invert_pat vl (env, fr) interp (p2, f) t
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
    | _ -> raise Exit

  (* interp x y <- t ? *)
  and invert_interp (env, fr) ls (t:term) = (*la ?*)
    let ld = Opt.get (find_logic_definition kn ls) in
    let vl, f = open_ls_defn ld in
    (*assert (oty_equal f.t_ty t.t_ty);*)
    if debug then Format.printf "invert_interp ls %a t %a@."
                                Pretty.print_ls ls Pretty.print_term t;
    match f.t_node, t.t_node with
    | Tcase (x, bl), _ ->
       (*FIXME*)
       assert (List.length vl = 2);
       (match x.t_node with Tvar v when vs_equal v (List.hd vl) -> () | _ -> assert false);
       if debug then Format.printf "case match@.";
       let rec aux = function
         | [] -> raise Exit
         | tb::l ->
            try invert_pat vl (env, fr) ls (t_open_branch tb) t
            with Exit -> if debug then Format.printf "match failed@."; aux l in
       aux bl
    | _ -> raise Exit
  in
  let reify_term (env, fr, subst) (lv, vy) t rt =
    if debug then Format.printf "reify_term %a@." Pretty.print_term t;
    match t.t_node, rt.t_node with
    | _, Tapp(interp, [{t_node = Tvar vx}; {t_node = Tvar vy'} ])
         when oty_equal t.t_ty interp.ls_value && Svs.mem vx lv && vs_equal vy vy' ->
       if debug then Format.printf "case interp@.";
       let env, fr, x = invert_interp (env, fr) interp t in
       env, fr, Mvs.add vx x subst (*t_app interp [x; y] (Some ty_val)*)
    | _ ->
       (*if debug then
       Format.printf "wrong type: t.ty %a interp.ls_value %a@."
                     Pretty.print_ty (Opt.get t.t_ty)
                     Pretty.print_ty (Opt.get interp.ls_value);*)
       raise Exit
  in
  let g, prev = Task.task_separate_goal task in
  let g = Apply.term_decl g in
  try
    if debug then Format.printf "start@.";
    let d = Apply.find_hypothesis pr.pr_name prev in
    if d = None then raise Exit;
    let d = Opt.get d in
    let l = Apply.term_decl d in
    let (lp, lv, rt) = Apply.intros l in
    begin match (rt.t_node, g.t_node) with
    | (Tapp(eq, [({t_node = Tapp(interp, [{t_node = Tvar x1};
                                          {t_node = Tvar vy}])} as rt1);
                 ({t_node = Tapp(interp', [{t_node = Tvar x2};
                                           {t_node = Tvar vy'}])} as rt2)]),
       Tapp(eq', [t1; t2]))
         when ls_equal eq ps_equ && ls_equal eq' ps_equ
              && ls_equal interp interp' && vs_equal vy vy' && Svs.mem x1 lv
              && Svs.mem x2 lv && Svs.mem vy lv->
       if debug then Format.printf "matched lemma conclusion@.";
       let ty_vars, ty_val = match interp.ls_args, interp.ls_value with
         | [ _ty_target; ty_vars ], Some ty_val
              when ty_equal ty_vars (ty_func ty_int ty_val)
           -> ty_vars, ty_val
         | _ -> raise Exit in
       let ly = create_fsymbol (Ident.id_fresh "y") [] ty_vars in
       let y = t_app ly [] (Some ty_vars) in
       let subst = Mvs.empty in
        let subst = Mvs.add vy y subst in
       let (env, fr, subst) =
         reify_term (Mterm.empty, 0, subst) (lv, vy) t1 rt1 in
       let (env, _fr, subst) =
         reify_term (env, fr, subst) (lv, vy) t2 rt2 in
       let inst_rt = t_subst subst rt in
       let inst_lp = List.map (t_subst subst) lp in
       if debug then Format.printf "building y map@.";
       if not (Svs.for_all (fun v -> Mvs.mem v subst) lv)
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
                    env prev in
       if debug then Format.printf "building goals@.";
       let d_r = create_prop_decl Paxiom
                                  (create_prsymbol (id_fresh "HR")) inst_rt in
       let pr = create_prsymbol
                  (id_fresh "GR"
                            ~label:(Slab.singleton expl_reification_check)) in
       let d = create_prop_decl Pgoal pr g in
       let task_r = Task.add_decl (Task.add_decl prev d_r) d in
       let ci = t_and (t_equ (t_subst subst rt1) t1)
                      (t_equ (t_subst subst rt2) t2) in
       let ltask_r = Trans.apply (Cut.cut ci (Some "interp")) task_r in
       let lt = List.map (fun ng -> Task.add_decl prev (create_prop_decl Pgoal
                             (create_prsymbol (id_fresh "G")) ng)) inst_lp in
       ltask_r@lt
    | _ -> raise Exit
    end
  with Exit -> [task])

let () = wrap_and_register
           ~desc:"reflection_l <prop> attempts to prove the goal by reflection using the lemma prop"
           "reflection_l"
           (Tprsymbol Ttrans_l) reflection_by_lemma

(*
Local Variables:
compile-command: "unset LANG; make -C ../.."
End:
*)
