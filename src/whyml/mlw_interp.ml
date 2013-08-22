
open Term

(* environment *)

open Mlw_ty

type env = {
  mknown : Mlw_decl.known_map;
  tknown : Decl.known_map;
(*
  pvsenv : term Mpv.t;
*)
  vsenv : term Mvs.t;
}

(*
let bind_pvs v t env = { env with pvsenv = Mpv.add v t env.pvsenv }
*)

let bind_vs v t env = { env with vsenv = Mvs.add v t env.vsenv }

let multibind_vs l tl env =
  try
    List.fold_right2 bind_vs l tl env
  with Invalid_argument _ -> assert false

exception NoMatch
exception Undetermined

let rec matching env t p =
  match p.pat_node,t.t_node with
  | Pwild, _ -> env
  | Pvar v, _ -> bind_vs v t env
  | Papp(ls1,pl), Tapp(ls2,tl) ->
    if ls_equal ls1 ls2 then
      List.fold_left2 matching env tl pl
    else
      if ls2.ls_constr > 0 then raise NoMatch
      else raise Undetermined
  | Papp _, _ -> raise Undetermined
  | Por _, _ -> raise Undetermined
  | Pas _, _ -> raise Undetermined


(* builtin symbols *)

let computer_div_mod_big_int x y =
  let q,r = Big_int.quomod_big_int x y in
  (* we have x = q*y + r with 0 <= r < |y| *)
  if Big_int.sign_big_int x < 0 then
    if Big_int.sign_big_int y < 0 then
      (Big_int.pred_big_int q, Big_int.add_big_int r y)
    else
      (Big_int.succ_big_int q, Big_int.sub_big_int r y)
  else (q,r)

let computer_div_big_int x y =
  fst (computer_div_mod_big_int x y)

let computer_mod_big_int x y =
  snd (computer_div_mod_big_int x y)

let builtins = Hls.create 17

let ls_minus = ref ps_equ (* temporary *)

let term_of_big_int i =
  if Big_int.sign_big_int i >= 0 then
    let s = Big_int.string_of_big_int i in
    t_const (Number.ConstInt (Number.int_const_dec s))
  else
    let i = Big_int.minus_big_int i in
    let s = Big_int.string_of_big_int i in
    let c = t_const (Number.ConstInt (Number.int_const_dec s)) in
    t_app_infer !ls_minus [c]

exception NotNum

let rec big_int_of_term t =
  match t.t_node with
    | Tconst (Number.ConstInt i) -> Number.compute_int i
    | Tapp(ls,[t1]) when ls_equal ls !ls_minus ->
      let i = big_int_of_term t1 in
      Big_int.minus_big_int i
    | _ -> raise NotNum

let eval_int_op op ls l =
  match l with
  | [t1;t2] ->
    begin
      try
        let i1 = big_int_of_term t1 in
        let i2 = big_int_of_term t2 in
        term_of_big_int (op i1 i2)
      with NotNum | Division_by_zero ->
        t_app_infer ls [t1;t2]
    end
  | _ -> assert false

let eval_int_uop op ls l =
  match l with
  | [t1] ->
    begin
      try
        let i1 = big_int_of_term t1 in
        term_of_big_int (op i1)
      with NotNum ->
        t_app_infer ls [t1]
    end
  | _ -> assert false

let eval_int_rel op ls l =
  match l with
  | [t1;t2] ->
    begin
      try
        let i1 = big_int_of_term t1 in
        let i2 = big_int_of_term t2 in
        if op i1 i2 then t_true else t_false
      with NotNum ->
        t_app_infer ls [t1;t2]
    end
  | _ -> assert false

let eval_equ _ls l =
  match l with
  | [t1;t2] ->
    if t_equal_alpha t1 t2 then t_true else
      begin
        try
          let i1 = big_int_of_term t1 in
          let i2 = big_int_of_term t2 in
          if Big_int.eq_big_int i1 i2 then
            t_true else t_false
        with NotNum ->
          match t1.t_node,t2.t_node with
            | Ttrue, Tfalse | Tfalse, Ttrue -> t_false
            | _ -> t_equ t1 t2
      end
  | _ -> assert false

let built_in_theories =
  [ ["int"],"Int",
    [ "infix +", eval_int_op Big_int.add_big_int;
      "infix -", eval_int_op Big_int.sub_big_int;
      "infix *", eval_int_op Big_int.mult_big_int;
      "prefix -", eval_int_uop Big_int.minus_big_int;
      "infix <", eval_int_rel Big_int.lt_big_int;
      "infix <=", eval_int_rel Big_int.le_big_int;
      "infix >", eval_int_rel Big_int.gt_big_int;
      "infix >=", eval_int_rel Big_int.ge_big_int;
    ] ;
    ["int"],"ComputerDivision",
    [ "div", eval_int_op computer_div_big_int;
      "mod", eval_int_op computer_mod_big_int;
    ] ;
    ["int"],"EuclideanDivision",
    [ "div", eval_int_op Big_int.div_big_int;
      "mod", eval_int_op Big_int.mod_big_int;
    ] ;
  ]

let add_builtin_th env (l,n,d) =
  try
    let th = Env.find_theory env l n in
    List.iter
      (fun (id,f) ->
        let ls = Theory.ns_find_ls th.Theory.th_export [id] in
        if id = "prefix -" then
          ls_minus := ls;
        Hls.add builtins ls f)
      d
  with Not_found -> ()


let get_builtins env =
  Hls.add builtins ps_equ eval_equ;
  List.iter (add_builtin_th env) built_in_theories


let rec eval_term env ty t =
  let eval_rec t = eval_term env t.t_ty t in
  match t.t_node with
  | Tvar x ->
    begin try Mvs.find x env.vsenv
      with Not_found -> t
    end
  | Tbinop(Tand,t1,t2) ->
    t_and_simp (eval_rec t1) (eval_rec t2)
  | Tbinop(Tor,t1,t2) ->
    t_or_simp (eval_rec t1) (eval_rec t2)
  | Tbinop(Timplies,t1,t2) ->
    t_implies_simp (eval_rec t1) (eval_rec t2)
  | Tbinop(Tiff,t1,t2) ->
    t_iff_simp (eval_rec t1) (eval_rec t2)
  | Tnot t1 -> t_not_simp (eval_rec t1)
  | Tapp(ls,tl) ->
    eval_app env ty ls (List.map eval_rec tl)
  | Tif(t1,t2,t3) ->
    let u = eval_rec t1 in
    begin match u.t_node with
    | Ttrue -> eval_term env ty t2
    | Tfalse -> eval_term env ty t3
    | _ -> t_if u t2 t3
    end
  | Tlet(t1,tb) ->
    let u = eval_rec t1 in
    let v,t2 = t_open_bound tb in
    eval_term (bind_vs v u env) ty t2
  | Tcase(t1,tbl) ->
    let u = eval_rec t1 in
    eval_match env ty u tbl
  | Tquant _
  | Teps _
  | Tconst _
  | Ttrue
  | Tfalse -> t

and eval_match env ty u tbl =
  let rec iter tbl =
    match tbl with
    | [] ->
      Format.eprintf "Pattern matching not exhaustive in evaluation ???@.";
      exit 2
    | b::rem ->
      let p,t = t_open_branch b in
      try
        let env' = matching env u p in
        eval_term env' ty t
      with NoMatch -> iter rem
  in
  try iter tbl with Undetermined -> t_case u tbl

and eval_app env ty ls tl =
  try
    let f = Hls.find builtins ls in
    f ls tl
  with Not_found ->
    match
      try
        Decl.find_logic_definition env.tknown ls
      with Not_found ->
        Format.eprintf "lsymbol %s not found in term evaluation@."
          ls.ls_name.Ident.id_string;
        exit 2
    with
    | None ->
      begin try
        t_app_infer_inst ls tl ty
        with e ->
          Format.eprintf "@[<hov 2>Exception during term evaluation (t_app %s):@ %a@\nty = %a,@ tl = %a@]@."
            ls.ls_name.Ident.id_string
            Exn_printer.exn_printer e
            (Pp.print_option Pretty.print_ty) ty
            (Pp.print_list Pp.comma Pretty.print_term) tl
          ;
          exit 2
      end
    | Some d ->
      let l,t = Decl.open_ls_defn d in
      let env' = multibind_vs l tl env in
      eval_term env' ty t



let eval_global_term env km t =
  get_builtins env;
  let env =
    { mknown = Ident.Mid.empty;
      tknown = km;
(*
      pvsenv = Mpv.empty;
*)
      vsenv = Mvs.empty;
    }
  in
  eval_term env t.t_ty t



(* evaluation of WhyML expressions *)

open Mlw_expr

type result =
  | Normal of term
  | Excep of xsymbol * term
  | Irred of expr
  | Fun of psymbol * lambda * pvsymbol list * int

let print_result fmt r =
  match r with
    | Normal t ->
      Format.fprintf fmt "@[%a@]" Pretty.print_term t
    | Excep(x,t) ->
      Format.fprintf fmt "@[exception %s(@[%a@])@]"
        x.xs_name.Ident.id_string Pretty.print_term t
    | Irred e ->
      Format.fprintf fmt "@[Cannot execute expression@ @[%a@]@]"
        Mlw_pretty.print_expr e
    | Fun _ ->
      Format.fprintf fmt "@[Result is a function@]"

type state = unit

let print_state fmt _s =
  Format.fprintf fmt "TODO"

let rec eval_expr env (s:state) (e : expr) : result * state =
  match e.e_node with
  | Elogic t -> Normal (eval_term env t.t_ty t), s
  | Evalue pvs -> 
    begin
      try let t = Mvs.find pvs.pv_vs env.vsenv in
          Normal t,s
      with Not_found -> Irred e, s
    end
  | Elet(ld,e1) ->
    begin match ld.let_sym with
      | LetV pvs ->
        begin match eval_expr env s ld.let_expr with
          | Normal t,s' ->
(*
            eval_expr (bind_pvs pvs t env) e1
*)
            eval_expr (bind_vs pvs.pv_vs t env) s' e1
          | r -> r
        end
      | LetA _ -> Irred e, s
    end
  | Eapp(e,pvs,_spec) ->
    begin match eval_expr env s e with
      | Fun(ps,lam,args,n), s' ->
        if n > 1 then
          Fun(ps,lam,pvs::args,n-1), s'
        else
        let args = List.rev (pvs::args) in
        let params = List.map (fun pvs -> pvs.pv_vs) lam.l_args in
        let args = List.map (fun pvs -> Mvs.find pvs.pv_vs env.vsenv) args in
        let env' = multibind_vs params args env in
        eval_expr env' s' lam.l_expr
      | _ -> Irred e, s
    end
  | Earrow ps -> 
    begin
      let d =
        try
          Mlw_decl.find_definition env.mknown ps
        with Not_found ->
          Format.eprintf "psymbol %s not found in execution@."
            ps.ps_name.Ident.id_string;
          exit 2
      in
      let lam = d.fun_lambda in
      Fun(ps,lam,[], List.length lam.l_args),s
    end
  | Eif(e1,e2,e3) ->
    begin
      match eval_expr env s e1 with
        | Normal t, s' ->
          begin
            match t.t_node with
              | Ttrue -> eval_expr env s' e2
              | Tfalse -> eval_expr env s' e3
              | _ ->
                Format.eprintf "@[Cannot interp condition of if: @[%a@]@]@."
                  Pretty.print_term t;
                Irred e, s
          end
        | r -> r
    end
  | Eraise(xs,e1) ->
    begin
      let r,s' = eval_expr env s e1 in
      match r with
        | Normal t -> Excep(xs,t),s'
        | _ -> r,s'
    end
  | Etry(e1,el) ->
    begin
      let r = eval_expr env s e1 in
      match r with
        | Excep(ex,t), s' ->
          let rec find_exc l =
            match l with
              | [] -> r
              | (xs,pvs,e2)::rem ->
                if xs_equal ex xs then
                  let env' = bind_vs pvs.pv_vs t env in
                  eval_expr env' s' e2
                else find_exc rem
          in
          find_exc el
        | _ -> r
    end
  | Eloop(_inv,_var,e1) ->
    begin
      let r = eval_expr env s e1 in
      match r with
        | Normal _, s' -> eval_expr env s' e
        | _ -> r
    end
  | Ecase(e1,ebl) ->
    begin
      match eval_expr env s e1 with
        | Normal t, s' ->
          begin try exec_match env t s' ebl
            with Undetermined -> Irred e, s
          end
        | r -> r
    end
  | Erec _
  | Eassign _
  | Eghost _
  | Eany _
  | Efor _
  | Eabstr _
  | Eassert _
  | Eabsurd ->
    Format.eprintf "@[Unsupported expression: @[%a@]@]@."
                  Mlw_pretty.print_expr e;
    Irred e, s

and exec_match env t s ebl =
  let rec iter ebl =
    match ebl with
    | [] ->
      Format.eprintf "Pattern matching not exhaustive in evaluation ???@.";
      exit 2
    | (p,e)::rem ->
      try
        let env' = matching env t p.ppat_pattern in
        eval_expr env' s e
      with NoMatch -> iter rem
  in
  iter ebl


let eval_global_expr env mkm tkm e =
  get_builtins env;
  let env = {
    mknown = mkm;
    tknown = tkm;
(*
    pvsenv = Mpv.empty;
*)
    vsenv = Mvs.empty;
  }
  in
  eval_expr env () e
