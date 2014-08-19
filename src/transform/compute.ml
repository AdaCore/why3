
open Term
open Decl
open Task
open Theory

(* obsolete

type env = {
  tknown : Decl.known_map;
  vsenv : term Mvs.t;
}

let bind_vs v t env =
  { env with vsenv = Mvs.add v t env.vsenv }

let multibind_vs l tl env =
  try
    List.fold_right2 bind_vs l tl env
  with Invalid_argument _ -> assert false

let get_vs env vs =
  try Mvs.find vs env.vsenv
  with Not_found ->
    Format.eprintf "[Compute] logic variable %s not found in env@." vs.vs_name.Ident.id_string;
    raise Not_found





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




(* builtin symbols *)

let builtins = Hls.create 17

let ls_minus = ref ps_equ (* temporary *)

(* all builtin functions *)

let const_equality c1 c2 =
  match c1,c2 with
  | Number.ConstInt i1, Number.ConstInt i2 ->
    BigInt.eq (Number.compute_int i1) (Number.compute_int i2)
  | _ -> raise Undetermined

let value_equality t1 t2 =
  match (t1.t_node,t2.t_node) with
  | Tconst c1, Tconst c2 -> const_equality c1 c2
  | _ -> raise Undetermined

let to_bool b = if b then t_true else t_false

let eval_equ _ls l _ty =
  match l with
  | [t1;t2] ->
    begin
      try to_bool (value_equality t1 t2)
      with Undetermined -> t_equ t1 t2
    end
  | _ -> assert false


let eval_true _ls _l _ty = t_true

let eval_false _ls _l _ty = t_false

exception NotNum

let big_int_of_const c =
  match c with
    | Number.ConstInt i -> Number.compute_int i
    | _ -> raise NotNum

let const_of_big_int n =
  t_const (Number.ConstInt (Number.int_const_dec (BigInt.to_string n)))

let eval_int_op op ls l ty =
  match l with
  | [{t_node = Tconst c1};{t_node = Tconst c2}] ->
    begin
      try const_of_big_int (op (big_int_of_const c1) (big_int_of_const c2))
      with NotNum | Division_by_zero ->
        t_app ls l ty
    end
  | _ -> t_app ls l ty


let built_in_theories =
  [ ["bool"],"Bool", [],
    [ "True", None, eval_true ;
      "False", None, eval_false ;
    ] ;
    ["int"],"Int", [],
    [ "infix +", None, eval_int_op BigInt.add;
      "infix -", None, eval_int_op BigInt.sub;
      "infix *", None, eval_int_op BigInt.mul;
(*
      "prefix -", Some ls_minus, eval_int_uop BigInt.minus;
      "infix <", None, eval_int_rel BigInt.lt;
      "infix <=", None, eval_int_rel BigInt.le;
      "infix >", None, eval_int_rel BigInt.gt;
      "infix >=", None, eval_int_rel BigInt.ge;
*)
    ] ;
(*
    ["int"],"MinMax", [],
    [ "min", None, eval_int_op BigInt.min;
      "max", None, eval_int_op BigInt.max;
    ] ;
    ["int"],"ComputerDivision", [],
    [ "div", None, eval_int_op BigInt.computer_div;
      "mod", None, eval_int_op BigInt.computer_mod;
    ] ;
    ["int"],"EuclideanDivision", [],
    [ "div", None, eval_int_op BigInt.euclidean_div;
      "mod", None, eval_int_op BigInt.euclidean_mod;
    ] ;
    ["map"],"Map", ["map", builtin_map_type],
    [ "const", Some ls_map_const, eval_map_const;
      "get", Some ls_map_get, eval_map_get;
      "set", Some ls_map_set, eval_map_set;
    ] ;
*)
  ]

let add_builtin_th env (l,n,t,d) =
  try
    let th = Env.find_theory env l n in
    List.iter
      (fun (id,r) ->
        let ts = Theory.ns_find_ts th.Theory.th_export [id] in
        r ts)
      t;
    List.iter
      (fun (id,r,f) ->
        let ls = Theory.ns_find_ls th.Theory.th_export [id] in
        Hls.add builtins ls f;
        match r with
          | None -> ()
          | Some r -> r := ls)
      d
  with Not_found ->
    Format.eprintf "[Compute] theory %s not found@." n

let get_builtins env =
  Hls.clear builtins;
  Hls.add builtins ps_equ eval_equ;
  List.iter (add_builtin_th env) built_in_theories





(* computation in terms *)

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
  | Tapp(ls,tl) ->
    compute_app env ls (List.map eval_rec tl) t.t_ty
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
  | Tcase(t1,tbl) ->
    let u1 = eval_rec t1 in
    compute_match env u1 tbl
  | Teps _ -> t
  | Tquant _ -> t


and compute_match env u tbl =
  let rec iter tbl =
    match tbl with
    | [] ->
      Format.eprintf "[Compute] fatal error: pattern matching not exhaustive in evaluation.@.";
      assert false
    | b::rem ->
      let p,t = t_open_branch b in
      try
        let env' = matching env u p in
        compute_in_term env' t
      with NoMatch -> iter rem
  in
  try iter tbl with Undetermined ->
    t_case u tbl


and compute_app env ls tl ty =
  try
    let f = Hls.find builtins ls in
    f ls tl ty
  with Not_found ->
    try
      let d = Ident.Mid.find ls.ls_name env.tknown in
      match d.Decl.d_node with
      | Decl.Dtype _ | Decl.Dprop _ -> assert false
      | Decl.Dlogic dl ->
        (* regular definition *)
        let d = List.assq ls dl in
        let l,t = Decl.open_ls_defn d in
        let env' = multibind_vs l tl env in
        compute_in_term env' t
      | Decl.Dparam _ | Decl.Dind _ ->
        t_app ls tl ty
      | Decl.Ddata dl ->
        (* constructor or projection *)
        match tl with
        | [ { t_node = Tapp(ls1,tl1) } ] ->
          (* if ls is a projection and ls1 is a constructor,

             we should compute that projection *)
          let rec iter dl =
            match dl with
            | [] -> t_app ls tl ty
            | (_,csl) :: rem ->
              let rec iter2 csl =
                match csl with
                | [] -> iter rem
                | (cs,prs) :: rem2 ->
                  if ls_equal cs ls1
                  then
                    (* we found the right constructor *)
                    let rec iter3 prs tl1 =
                      match prs,tl1 with
                      | (Some pr)::prs, t::tl1 ->
                        if ls_equal ls pr
                        then (* projection found! *) t
                        else
                          iter3 prs tl1
                      | None::prs, _::tl1 ->
                        iter3 prs tl1
                      | _ -> t_app ls tl ty
                    in iter3 prs tl1
                  else iter2 rem2
              in iter2 csl
          in iter dl
        | _ -> t_app ls tl ty
    with Not_found ->
      Format.eprintf "[Compute] definition of logic symbol %s not found@."
        ls.ls_name.Ident.id_string;
      t_app ls tl ty

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

let compute env task =
  let task = compute_in_task task in
  match task with
  | Some
      { task_decl =
          { td_node = Decl { d_node = Dprop (Pgoal, _, f) }}
      } ->
    get_builtins env;
    begin match f.t_node with
    | Ttrue -> []
    | _ -> [task]
    end
  | _ -> assert false

let () =
  Trans.register_env_transform_l "compute"
    (fun env -> Trans.store (compute env))
    ~desc:"Compute@ as@ much@ as@ possible"

  *)


(* compute with rewrite rules *)



let collect_rule_decl prs e d =
  match d.Decl.d_node with
    | Decl.Dtype _ | Decl.Ddata _ | Decl.Dparam _ | Decl.Dind  _
    | Decl.Dlogic _ -> e
    | Decl.Dprop(_, pr, t) ->
      if Decl.Spr.mem pr prs then
        Reduction_engine.add_rule t e
      else e

let collect_rules env km prs t =
  Task.task_fold
    (fun e td -> match td.Theory.td_node with
      | Theory.Decl d -> collect_rule_decl prs e d
      | _ -> e)
    (Reduction_engine.create env km) t

let normalize_goal env (prs : Decl.Spr.t) task =
  match task with
  | Some
      { task_decl =
          { td_node = Decl { d_node = Dprop (Pgoal, pr, f) } };
        task_prev = prev;
        task_known = km;
      } ->
    let engine = collect_rules env km prs task in
    let f = Reduction_engine.normalize engine f in
    begin match f.t_node with
    | Ttrue -> []
    | _ ->
      let d = Decl.create_prop_decl Pgoal pr f in
      [Task.add_decl prev d]
    end
  | _ -> assert false


let meta = Theory.register_meta "rewrite" [Theory.MTprsymbol]
  ~desc:"Declares@ the@ given@ prop@ as@ a@ rewrite@ rule."

let normalize_transf env =
  Trans.on_tagged_pr meta (fun prs -> Trans.store (normalize_goal env prs))

let () = Trans.register_env_transform_l "compute_in_goal" normalize_transf
  ~desc:"Normalize@ terms@ with@ respect@ to@ rewrite@ rules@ declared as metas"
