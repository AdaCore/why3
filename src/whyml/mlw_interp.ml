
open Term

let eval_app ls tl ty =
  if ls_equal ls ps_equ then
    match tl with
    | [t1;t2] ->
      if t_equal_alpha t1 t2 then t_true else
        t_app ls tl ty
(* TODO later
        begin match t1.t_node,t2.t_node with
        | Ttrue, Tfalse | Tfalse, Ttrue -> t_false
        | Const c1, Const c2 -> eval_const ...
*)
    | _ -> assert false
  else
    (* TODO : if has_definition ls then ... *)
    try
      t_app ls tl ty
    with e ->
      Format.eprintf "Exception during term evaluation (t_app_infer %s): %a@."
        ls.ls_name.Ident.id_string
        Exn_printer.exn_printer e;
      exit 2

exception NoMatch
exception Undetermined

let rec matching env t p =
  match p.pat_node,t.t_node with
  | Pwild, _ -> env
  | Pvar v, _ -> Mvs.add v t env
  | Papp(ls1,pl), Tapp(ls2,tl) ->
    if ls_equal ls1 ls2 then
      List.fold_left2 matching env tl pl
    else
      if ls2.ls_constr > 0 then raise NoMatch
      else raise Undetermined
  | Papp _, _ -> raise Undetermined
  | Por _, _ -> raise Undetermined
  | Pas _, _ -> raise Undetermined


let rec eval_term menv env t =
  match t.t_node with
  | Tvar x ->
    begin try Mvs.find x env
      with Not_found -> t
    end
  | Tbinop(Tand,t1,t2) ->
    t_and_simp (eval_term menv env t1) (eval_term menv env t2)
  | Tbinop(Tor,t1,t2) ->
    t_or_simp (eval_term menv env t1) (eval_term menv env t2)
  | Tbinop(Timplies,t1,t2) ->
    t_implies_simp (eval_term menv env t1) (eval_term menv env t2)
  | Tbinop(Tiff,t1,t2) ->
    t_iff_simp (eval_term menv env t1) (eval_term menv env t2)
  | Tnot t1 -> t_not_simp (eval_term menv env t1)
  | Tapp(ls,tl) ->
    eval_app ls (List.map (eval_term menv env) tl) t.t_ty
  | Tif(t1,t2,t3) ->
    let u = eval_term menv env t1 in
    begin match u.t_node with
    | Ttrue -> eval_term menv env t2
    | Tfalse -> eval_term menv env t3
    | _ -> t_if u t2 t3
    end
  | Tlet(t1,tb) ->
    let u = eval_term menv env t1 in
    let v,t2 = t_open_bound tb in
    eval_term menv (Mvs.add v u env) t2
  | Tcase(t1,tbl) ->
    let u = eval_term menv env t1 in
    eval_match menv env u tbl
  | Tquant _
  | Teps _
  | Tconst _
  | Ttrue
  | Tfalse -> t

and eval_match menv env u tbl =
  let rec iter tbl =
    match tbl with
    | [] ->
      Format.eprintf "Pattern matching not exhaustive in evaluation ???@.";
      exit 2
    | b::rem ->
      let p,t = t_open_branch b in
      try
        let env' = matching env u p in
        eval_term menv env' t
      with NoMatch -> iter rem
  in
  try iter tbl with Undetermined -> t_case u tbl
