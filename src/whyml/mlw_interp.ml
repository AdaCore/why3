
open Term

let eval_app ls tl =
  if ls_equal ls ps_equ then
    match tl with
    | [t1;t2] ->
      if t_equal_alpha t1 t2 then t_true else
        t_app_infer ls tl
(* TODO later
        begin match t1.t_node,t2.t_node with
        | Ttrue, Tfalse | Tfalse, Ttrue -> t_false
        | Const c1, Const c2 -> eval_const ...
*)
    | _ -> assert false
  else
    (* TODO : if has_definition ls then ... *)
    t_app_infer ls tl

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
    eval_app ls (List.map (eval_term menv env) tl)
  | Tif(t1,t2,t3) ->
    let u = eval_term menv env t1 in
    begin match u.t_node with
    | Ttrue -> eval_term menv env t2
    | Tfalse -> eval_term menv env t3
    | _ -> t_if u t2 t3
    end
  | Tlet(_t1,_tb) -> t (* TODO *)
  | Tcase(_t1,_tbl) -> t (* TODO *)
  | Tquant _
  | Teps _
  | Tconst _
  | Ttrue
  | Tfalse -> t
