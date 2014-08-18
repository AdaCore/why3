
open Term
open Decl
open Task
open Theory

type env = {
  tknown : Decl.known_map;
  vsenv : term Mvs.t;
}

let bind_vs v t env =
  { env with vsenv = Mvs.add v t env.vsenv }

let get_vs env vs =
  try Mvs.find vs env.vsenv
  with Not_found ->
    Format.eprintf "logic variable %s not found in env@." vs.vs_name.Ident.id_string;
    assert false

exception NoMatch
exception Undetermined
exception CannotCompute

let rec matching env t p =
  match p.pat_node with
  | Pwild -> env
  | Pvar v -> bind_vs v t env
  | Por(p1,p2) ->
    begin
      try matching env t p1
      with NoMatch -> matching env t p2
    end
  | Pas(p,v) -> matching (bind_vs v t env) t p
  | Papp(ls1,pl) ->
    match t.t_node with
      | Tapp(ls2,tl) ->
        if ls_equal ls1 ls2 then
          List.fold_left2 matching env tl pl
        else
          if ls2.ls_constr > 0 then raise NoMatch
          else raise Undetermined
      | _ -> raise Undetermined



let rec compute_in_term env t =
  let eval_rec = compute_in_term env in
  match t.t_node with
  | Ttrue | Tfalse | Tconst _ -> t
  | Tbinop(Tand,t1,t2) ->
    t_and_simp (eval_rec t1) (eval_rec t2)
  | Tbinop(Tor,t1,t2) ->
    t_or_simp (eval_rec t1) (eval_rec t2)
  | Tbinop(Timplies,t1,t2) ->
    t_implies_simp (eval_rec t1) (eval_rec t2)
  | Tbinop(Tiff,t1,t2) ->
    t_iff_simp (eval_rec t1) (eval_rec t2)
  | Tnot(t1) -> t_not_simp (eval_rec t1)
  | Tvar vs ->
    begin
      try get_vs env vs
      with Not_found -> t
    end
  | Tapp _ -> t
  | Tif(t1,t2,t3) ->
    let u1 = eval_rec t1 in
    begin match u1.t_node with
    | Ttrue -> eval_rec t2
    | Tfalse -> eval_rec t3
    | _ -> t_if u1 t2 t3
    end
  | Tlet(t1,tb) ->
    let u1 = eval_rec t1 in
    let v,t2 = t_open_bound tb in
    let u2 = compute_in_term (bind_vs v u1 env) t2 in
    t_let_close_simp v u1 u2
  | Tcase _ -> t
(*
  | Tcase(t1,tbl) ->
    let u1 = eval_rec t1 in
    compute_match env u1 tbl
*)
  | Teps _ -> t
  | Tquant _ -> t


(*
and compute_match env u tbl =
  let rec iter tbl =
    match tbl with
    | [] ->
      Format.eprintf "[Exec] fatal error: pattern matching not exhaustive in evaluation.@.";
      assert false
    | b::rem ->
      let p,t = t_open_branch b in
      try
        let env' = matching env u p in
        compute_in_term env' t
      with NoMatch -> iter rem
  in
  try iter tbl with Undetermined ->
    t_case_close_simp u tbl
*)

let compute_in_decl km d =
  match d.d_node with
  | Dprop(k,pr,f) ->
    let t = compute_in_term { tknown = km; vsenv = Mvs.empty } f in
    create_prop_decl k pr t
  | _ -> d

let compute_in_tdecl km d =
  match d.td_node with
  | Decl d -> create_decl (compute_in_decl km d)
  | _ -> d

let rec compute_in_task task =
  match task with
  | Some d ->
    add_tdecl
      (compute_in_task d.task_prev)
      (compute_in_tdecl d.task_known d.task_decl)
  | None -> None

let compute task =
  let task = compute_in_task task in
  match task with
  | Some
      { task_decl =
          { td_node = Decl { d_node = Dprop (Pgoal, _, f) }}
      } ->
    begin match f.t_node with
    | Ttrue -> []
    | _ -> [task]
    end
  | _ -> assert false

let () =
  Trans.register_transform_l "compute" (Trans.store compute)
    ~desc:"Compute@ as@ much@ as@ possible"
