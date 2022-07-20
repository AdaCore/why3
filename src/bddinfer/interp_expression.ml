

(** {1 Translation between expressions and abstract states}

TODO list:

- replace all debug [printf] into [Debug.dprintf]

*)


open Ast
open Apron
open Abstract

let make_cst : string -> Texpr1.expr = fun c ->
    Texpr1.Cst (Coeff.s_of_mpq (Mpq.of_string c))

let make_binop : Texpr1.binop -> Texpr1.expr -> Texpr1.expr -> Texpr1.expr = fun op e1 e2 ->
    Texpr1.Binop (op, e1, e2, Texpr1.Int, Texpr1.Zero)

let rec get_var env v =
  match VarMap.find v env with
  | RefValue x -> get_var env x
  | (IntValue _ | BoolValue _) as v -> v
  | exception Not_found ->
     Format.printf "[Interp_expression.get_var] v = %a env = %a@."
       print_var v print_env env;
     assert false

let rec to_texpr ~old (env: why_env) (e : expression) : Texpr1.expr =
    match e with
    | Evar (v, Here) ->
      begin
        match get_var env v with
        | IntValue x -> Texpr1.Var x
        | RefValue _ | BoolValue _ ->
           assert false (* should never reach this point *)
      end
    | Evar (v, Old) ->
      begin
        match get_var old v with
        | IntValue x -> Texpr1.Var x
        | RefValue _ | BoolValue _ ->
           assert false (* should never reach this point *)
      end
    | Ecst c -> make_cst c
    | Eadd (e1, e2) -> make_binop Texpr1.Add (to_texpr ~old env e1) (to_texpr ~old env e2)
    | Esub (e1, e2) -> make_binop Texpr1.Sub (to_texpr ~old env e1) (to_texpr ~old env e2)
    | Emul (e1, e2) -> make_binop Texpr1.Mul (to_texpr ~old env e1) (to_texpr ~old env e2)
    | Ediv (e1, e2) -> make_binop Texpr1.Div (to_texpr ~old env e1) (to_texpr ~old env e2)
    | Emod (e1, e2) -> make_binop Texpr1.Mod (to_texpr ~old env e1) (to_texpr ~old env e2)
    | Ebwtrue
    | Ebwfalse
    | Ebwnot _
    | Ebwand _
    | Ebwor _ ->
       assert false (* no Boolean expression here *)

let atomic_condition_to_tcons ~old (a : t) (c:atomic_condition) : Tcons1.t =
    let whyenv = why_env a in
    let env = apron_env a in
    match c with
    | Ceq (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e1 e2) |> Texpr1.of_expr env in
        Tcons1.make e Tcons1.EQ
    | Cne (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e1 e2) |> Texpr1.of_expr env in
        Tcons1.make e Tcons1.DISEQ
    | Cge (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e1 e2) |> Texpr1.of_expr env in
        Tcons1.make e Tcons1.SUPEQ
    | Cgt (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e1 e2) |> Texpr1.of_expr env in
        Tcons1.make e Tcons1.SUP
    | Cle (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e2 e1) |> Texpr1.of_expr env in
        Tcons1.make e Tcons1.SUPEQ
    | Clt (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e2 e1) |> Texpr1.of_expr env in
        Tcons1.make e Tcons1.SUP
    | C_is_true _ | C_is_false _ | Ceq_bool _   | Cne_bool _ ->
       assert false

let to_expr ~old whyenv apronenv e =
  e |> to_texpr ~old whyenv |> Apron.Texpr1.of_expr apronenv


(** interpretation of Boolean expressions *)

let rec interp_bool_expr ~old env (e : expression) : B.t =
  match e with
  | Evar (v, Here) ->
     begin match get_var env v with
     | BoolValue v -> B.mk_var v
     | _ -> assert false
     end
  | Evar (v, Old) ->
     begin match get_var old v with
     | BoolValue v -> B.mk_var v
     | _ -> assert false
     end
  | Ebwand(e1,e2) ->
     B.mk_and (interp_bool_expr ~old env e1) (interp_bool_expr ~old env e2)
  | Ebwor(e1,e2) ->
     B.mk_or (interp_bool_expr ~old env e1) (interp_bool_expr ~old env e2)
  | Ebwnot(e) ->
     B.mk_not (interp_bool_expr ~old env e)
  | Ebwtrue -> B.one
  | Ebwfalse -> B.zero
  | Ecst _ | Eadd _ | Esub _ | Emul _ | Ediv _ | Emod _ -> assert false

let meet_atomic_condition ~old (state : t)  (c:atomic_condition) : t =
    match c with
    | Cne_bool (e1, e2) ->
        let env = why_env state in
        let b1 = interp_bool_expr ~old env e1 in
        let b2 = interp_bool_expr ~old env e2 in
        let b = B.(mk_iff b1 b2) in
        meet_with_bdd state (B.mk_not b)
    | Ceq_bool(e1,e2) ->
       let env = why_env state in
       let b1 = interp_bool_expr ~old env e1 in
       let b2 = interp_bool_expr ~old env e2 in
       let b = B.(mk_iff b1 b2) in
       meet_with_bdd state b
    | C_is_false e ->
       let env = why_env state in
       let b = interp_bool_expr ~old env e in
       let b = B.(mk_not b) in
       meet_with_bdd state b
    | C_is_true e ->
       let env = why_env state in
       let b = interp_bool_expr ~old env e in
       meet_with_bdd state b
    | _ ->
        let a = atomic_condition_to_tcons ~old state c in
        let apron_env = apron_env state in
        let array_cond = Tcons1.array_make apron_env 1 in
        Tcons1.array_set array_cond 0 a;
        meet_with_tcons_array state apron_env array_cond



let eadd e1 e2 =
  match e2 with
  | Ecst "0" -> e1
  | _ -> e_add e1 e2

let emul e coef =
  if Z.(coef = one) then e else e_mul e (e_cst (Z.to_string coef))

let lincons_to_expression m l =
  List.fold_left
    (fun e (v, c) ->
      match v with
      | Some(apron_var) ->
         let why_v = ApronVarMap.find apron_var m in
         eadd (emul (e_var why_v Here) c) e
      | None ->
         eadd (e_cst (Z.to_string c)) e)
    (e_cst "0") l

let lincons_to_condition m (t, l, r) =
  match t with
  | Lincons1.EQ -> c_eq_int (lincons_to_expression m l) (lincons_to_expression m r)
  | Lincons1.SUPEQ -> c_le (lincons_to_expression m r) (lincons_to_expression m l)
  | Lincons1.SUP -> c_lt (lincons_to_expression m r) (lincons_to_expression m l)
  | Lincons1.DISEQ -> c_ne_int (lincons_to_expression m l) (lincons_to_expression m r)
  | Lincons1.EQMOD _ -> assert false



let rec formula_to_atomic_condition env f =
  let open Bdd in
  let open Ast in
  match f with
  | Ftrue -> assert false
  | Ffalse -> assert false
  | Fvar v ->
     let x = BddVarMap.find v env in
     e_var x Here
  | Fnot (Fvar v) ->
     let x = BddVarMap.find v env in
     bwnot_simp (e_var x Here)
  | Fand(f1,f2) ->
     let f1 = formula_to_atomic_condition env f1 in
     let f2 = formula_to_atomic_condition env f2 in
     bwand_simp f1 f2
  | For(f1,f2) ->
     let f1 = formula_to_atomic_condition env f1 in
     let f2 = formula_to_atomic_condition env f2 in
     bwor_simp f1 f2
  | Fite(Fvar v,f1,f2) ->
     let x = BddVarMap.find v env in
     let f1 = formula_to_atomic_condition env f1 in
     let f2 = formula_to_atomic_condition env f2 in
     bwor_simp (bwand_simp (e_var x Here) f1)
       (bwand_simp (bwnot_simp (e_var x Here)) f2)
  | _ -> assert false (* not supposed to happen *)


let rec formula_to_conditions env acc f =
  let open Bdd in
  match f with
  | Ftrue -> acc
  | Ffalse -> Ast.false_cond::acc
  | Fand(f1,f2) ->
     formula_to_conditions env (formula_to_conditions env acc f1) f2
  | _ ->
     Ast.atomic_cond (Ast.c_is_true (formula_to_atomic_condition env f))::acc

let abstract_state_to_conditions s =
  let lincons = get_lincons s in
  let m = invert_varmap_int s in
  let integer_conditions =
    List.rev_map
      (fun c ->
        let c = Ast.atomic_cond (lincons_to_condition m c) in
(*
        if !Common.verbose >= 2 then
          Format.printf "@[Converted to integer condition @ @[%a@]@]@."
            Ast.print_condition c;
 *)
        c)
      (Array.to_list lincons)
  in
  let b = boolean_substate s in
  let f = B.as_compact_formula b in
  let m = invert_varmap_bool s in
(*
  if !Common.verbose >= 2 then
    Format.printf "@[Converting to Boolean condition @ @[@]@]@.";
 *)
  let c = formula_to_conditions m integer_conditions f in
(*
  if !Common.verbose >= 2 then
    Format.printf "@[Converted to some Boolean condition @ @[@]@]@.";
 *)
  c




(** meet an abstract state and a condition *)

let rec meet_condition ~old (state: t) (c:condition) : t =
    match c with
    | BTrue -> state
    | BFalse -> let env = why_env state in bottom env
    | BAnd (c1, c2) -> meet (meet_condition ~old state c1) (meet_condition ~old state c2)
    | BOr (c1, c2) -> join (meet_condition ~old state c1) (meet_condition ~old state c2)
    | BAtomic c ->
       meet_atomic_condition ~old state c


let meet_with_variable_equality state v1 v2 =
  let open Abstract in
  match v1, v2 with
  | BoolValue b1, BoolValue b2 ->
     let b = B.(mk_iff (mk_var b1) (mk_var b2)) in
     meet_with_bdd state b
  | IntValue n1, IntValue n2 ->
     let v1 = Texpr1.Var n1 in
     let v2 = Texpr1.Var n2 in
     let e = make_binop Texpr1.Sub v1 v2 in
     let env = apron_env state in
     let e = Texpr1.of_expr env e in
     let a = Tcons1.make e Tcons1.EQ in
     let apron_env = apron_env state in
     let array_cond = Tcons1.array_make apron_env 1 in
     Tcons1.array_set array_cond 0 a;
     meet_with_tcons_array state apron_env array_cond
  | _ -> assert false
