
open Term

exception NoMatch
exception Undetermined


let builtins = Hls.create 17

let const_of_big_int i =
(*
  if Big_int.sign_big_int i >= 0 then
*)
    let s = Big_int.string_of_big_int i in
    t_const (Number.ConstInt (Number.int_const_dec s))
(*
  else
*)

let op_const op c1 c2 =
  match c1,c2 with
  | Number.ConstInt i1, Number.ConstInt i2 ->
    let i1 = Number.compute_int i1 in
    let i2 = Number.compute_int i2 in
    op i1 i2
  | _ -> assert false

let uop_const op c =
  match c with
  | Number.ConstInt i ->
    let i = Number.compute_int i in op i
  | _ -> assert false

let bin_const op c1 c2 =
  let a = op_const op c1 c2 in
  const_of_big_int a

let unary_const op c =
  let a = uop_const op c in
  const_of_big_int a

let eval_int_op op ls l =
  match l with
  | [t1;t2] ->
    begin
      match t1.t_node, t2.t_node with
      | Tconst c1, Tconst c2 -> bin_const op c1 c2
      | _ -> t_app_infer ls [t1;t2]
    end
  | _ -> assert false

let eval_int_uop op ls l =
  match l with
  | [t1] ->
    begin
      match t1.t_node with
      | Tconst c1 -> unary_const op c1
      | _ -> t_app_infer ls [t1]
    end
  | _ -> assert false

let eval_int_rel op ls l =
  match l with
  | [t1;t2] ->
    begin
      match t1.t_node, t2.t_node with
      | Tconst c1, Tconst c2 ->
        if op_const op c1 c2 then t_true else t_false
      | _ -> t_app_infer ls [t1;t2]
    end
  | _ -> assert false

let eval_equ _ls l =
  match l with
  | [t1;t2] ->
    if t_equal_alpha t1 t2 then t_true else
      begin match t1.t_node,t2.t_node with
       | Ttrue, Tfalse | Tfalse, Ttrue -> t_false
       | Tconst c1, Tconst c2 ->
         if op_const Big_int.eq_big_int c1 c2 then
           t_true else t_false
       | _ -> t_equ t1 t2
      end
  | _ -> assert false


let built_in_theories =
  [ ["int"],"Int",
    [ "infix +", eval_int_op Big_int.add_big_int;
      "infix -", eval_int_op Big_int.sub_big_int;
      "infix *", eval_int_op Big_int.mult_big_int;
(* plante !
      "prefix -", eval_int_uop Big_int.minus_big_int;
*)
      "infix <", eval_int_rel Big_int.lt_big_int;
      "infix <=", eval_int_rel Big_int.le_big_int;
      "infix >", eval_int_rel Big_int.gt_big_int;
      "infix >=", eval_int_rel Big_int.ge_big_int;
    ]
  ]

let add_builtin_th env (l,n,d) =
  try
    let th = Env.find_theory env l n in
    List.iter
      (fun (id,f) ->
        let ls = Theory.ns_find_ls th.Theory.th_export [id] in
        Hls.add builtins ls f)
      d
  with Not_found -> ()


let get_builtins env =
  Hls.add builtins ps_equ eval_equ;
  List.iter (add_builtin_th env) built_in_theories

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


let rec eval_term km menv env t =
  match t.t_node with
  | Tvar x ->
    begin try Mvs.find x env
      with Not_found -> t
    end
  | Tbinop(Tand,t1,t2) ->
    t_and_simp (eval_term km menv env t1) (eval_term km menv env t2)
  | Tbinop(Tor,t1,t2) ->
    t_or_simp (eval_term km menv env t1) (eval_term km menv env t2)
  | Tbinop(Timplies,t1,t2) ->
    t_implies_simp (eval_term km menv env t1) (eval_term km menv env t2)
  | Tbinop(Tiff,t1,t2) ->
    t_iff_simp (eval_term km menv env t1) (eval_term km menv env t2)
  | Tnot t1 -> t_not_simp (eval_term km menv env t1)
  | Tapp(ls,tl) ->
    eval_app km menv env ls (List.map (eval_term km menv env) tl) t.t_ty
  | Tif(t1,t2,t3) ->
    let u = eval_term km menv env t1 in
    begin match u.t_node with
    | Ttrue -> eval_term km menv env t2
    | Tfalse -> eval_term km menv env t3
    | _ -> t_if u t2 t3
    end
  | Tlet(t1,tb) ->
    let u = eval_term km menv env t1 in
    let v,t2 = t_open_bound tb in
    eval_term km menv (Mvs.add v u env) t2
  | Tcase(t1,tbl) ->
    let u = eval_term km menv env t1 in
    eval_match km menv env u tbl
  | Tquant _
  | Teps _
  | Tconst _
  | Ttrue
  | Tfalse -> t

and eval_match km menv env u tbl =
  let rec iter tbl =
    match tbl with
    | [] ->
      Format.eprintf "Pattern matching not exhaustive in evaluation ???@.";
      exit 2
    | b::rem ->
      let p,t = t_open_branch b in
      try
        let env' = matching env u p in
        eval_term km menv env' t
      with NoMatch -> iter rem
  in
  try iter tbl with Undetermined -> t_case u tbl

and eval_app km menv env ls tl ty =
  try
    let f = Hls.find builtins ls in
    f ls tl
  with Not_found ->
    match
      try
        Decl.find_logic_definition km ls
      with Not_found ->
        Format.eprintf "lsymbol %s not found in term evaluation@."
          ls.ls_name.Ident.id_string;
        exit 2
    with
    | None ->
      begin try
        t_app ls tl ty
        with e ->
          Format.eprintf "@[<hov 2>Exception during term evaluation (t_app %s):@ %a@]@."
            ls.ls_name.Ident.id_string
            Exn_printer.exn_printer e;
          exit 2
      end
    | Some d ->
      let l,t = Decl.open_ls_defn d in
      let env' = List.fold_right2 Mvs.add l tl env in
      eval_term km menv env' t



let eval_term env km t =
  get_builtins env;
  eval_term km Mvs.empty Mvs.empty t
