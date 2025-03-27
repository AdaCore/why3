(********************************************************************)
(*                                                                  *)
(*  The Why3 Verification Platform   /   The Why3 Development Team  *)
(*  Copyright 2010-2024 --  Inria - CNRS - Paris-Saclay University  *)
(*                                                                  *)
(*  This software is distributed under the terms of the GNU Lesser  *)
(*  General Public License version 2.1, with the special exception  *)
(*  on linking described in file LICENSE.                           *)
(*                                                                  *)
(********************************************************************)


(** {1 Translation between expressions and abstract states}

TODO list:

- replace all debug [printf] into [Debug.dprintf]

*)


(* open Why3 *)
(* to comment out when inside Why3 *)

open Ast
open Apron
open Abstract

let rec get_var env v =
  match VarMap.find v env with
  | RefValue x -> get_var env x
  | (UnitValue | IntValue _ | BoolValue _) as v -> v
  | exception Not_found ->
     Format.printf "[Interp_expression.get_var] v = %a env = %a@."
       print_var v print_env env;
     assert false

(** interpretation of integer expressions *)

let make_cst : string -> Texpr1.expr = fun c ->
    Texpr1.Cst (Coeff.s_of_mpq (Mpq.of_string c))

let make_binop : Texpr1.binop -> Texpr1.expr -> Texpr1.expr -> Texpr1.expr = fun op e1 e2 ->
    Texpr1.Binop (op, e1, e2, Texpr1.Int, Texpr1.Zero)

let rec to_texpr ~old (env: why_env) (e : expression) : Texpr1.expr =
    match e with
    | Evar (v, Here) ->
      begin
        match get_var env v with
        | IntValue x -> Texpr1.Var x
        | UnitValue | RefValue _ | BoolValue _ ->
           assert false (* should never reach this point *)
      end
    | Evar (v, Old) ->
      begin
        match get_var old v with
        | IntValue x -> Texpr1.Var x
        | UnitValue | RefValue _ | BoolValue _ ->
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

let integer_condition_to_tcons ~old (a : t) (c:atomic_condition) : Tcons1.t =
    let whyenv = why_env a in
    match c with
    | Ceq (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e1 e2) |> of_apron_expr a in
        Tcons1.make e Tcons1.EQ
    | Cne (_e1, _e2) -> assert false
(*        let e = to_texpr ~old whyenv (e_sub e1 e2) |> of_apron_expr a in
        Tcons1.make e Tcons1.DISEQ
*)
    | Cge (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e1 e2) |> of_apron_expr a in
        Tcons1.make e Tcons1.SUPEQ
    | Cgt (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e1 e2) |> of_apron_expr a in
        Tcons1.make e Tcons1.SUP
    | Cle (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e2 e1) |> of_apron_expr a in
        Tcons1.make e Tcons1.SUPEQ
    | Clt (e1, e2) ->
        let e = to_texpr ~old whyenv (e_sub e2 e1) |> of_apron_expr a in
        Tcons1.make e Tcons1.SUP
    | C_is_true _ -> assert false (* no Boolean expression here *)

(** interpretation of Boolean expressions *)

let rec interp_bool_expr state ~old env (e : expression) : t =
  match e with
  | Evar (v, Here) ->
     begin match get_var env v with
     | BoolValue v -> singleton_boolean_var_true state v
     | _ -> assert false
     end
  | Evar (v, Old) ->
     begin match get_var old v with
     | BoolValue v -> singleton_boolean_var_true state v
     | _ -> assert false
     end
  | Ebwand(e1,e2) ->
     Abstract.meet (interp_bool_expr state ~old env e1) (interp_bool_expr state ~old env e2)
  | Ebwor(e1,e2) ->
     Abstract.join (interp_bool_expr state ~old env e1) (interp_bool_expr state ~old env e2)
  | Ebwnot(e) ->
     Abstract.complement (interp_bool_expr state ~old env e)
  | Ebwtrue -> top state
  | Ebwfalse -> bottom state
  | Ecst _ | Eadd _ | Esub _ | Emul _ | Ediv _ | Emod _ -> assert false


let rec meet_atomic_condition ~old (state : t)  (c:atomic_condition) : t =
  let env = why_env state in
  match c with
  | C_is_true e ->
    let b = interp_bool_expr state ~old env e in
    meet state b
  | Cne(e1,e2) ->
    let s1 = meet_atomic_condition ~old state (c_lt e1 e2) in
    let s2 = meet_atomic_condition ~old state (c_gt e1 e2) in
    join s1 s2
  | _ ->
    let a = integer_condition_to_tcons ~old state c in
    (* Format.eprintf "@[meet_atomic_condition with state:@ @[%a@]@]@." Abstract.print state; *)
    let s = Abstract.meet_with_apron_constraint state a in
    (* Format.eprintf "@[after meet_atomic_condition:@ @[%a@]@]@." Abstract.print s; *)
    s





(** meet an abstract state and a condition *)

let rec meet_condition ~old (state: t) (c:condition) : t =
    match c with
    | BTrue -> state
    | BFalse -> bottom state
    | BAnd (c1, c2) -> meet (meet_condition ~old state c1) (meet_condition ~old state c2)
    | BOr (c1, c2) -> join (meet_condition ~old state c1) (meet_condition ~old state c2)
    | Bite _ -> assert false
    | BAtomic c ->
       meet_atomic_condition ~old state c

let utime () = Unix.((times ()).tms_utime)

let time_in_meet_condition = ref 0.0

let meet_condition ~old s c =
  let t = utime () in
  let s = meet_condition ~old s c in
  time_in_meet_condition := !time_in_meet_condition +. (utime () -. t);
  s







(* conversion of abstract states back to conditions *)


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



let rec formula_to_condition mb mi fi f =
  let open Bddparam in
  let open B in
  let open Ast in
  match f with
  | Ftrue -> true_cond
  | Ffalse -> false_cond
  | Fvar v ->
     let x = BddVarMap.find v mb in
     atomic_cond (c_is_true (e_var x Here))
  | Fnot (Fvar v) ->
     let x = BddVarMap.find v mb in
     atomic_cond (c_is_false (e_var x Here))
  | Fnot _ -> assert false (* should not happen *)
  | Fand(f1,f2) ->
     let f1 = formula_to_condition mb mi fi f1 in
     let f2 = formula_to_condition mb mi fi f2 in
     and_cond f1 f2
  | For(f1,f2) ->
     let f1 = formula_to_condition mb mi fi f1 in
     let f2 = formula_to_condition mb mi fi f2 in
     or_cond f1 f2
  | Fite(Fvar v,f1,f2) ->
     let x = BddVarMap.find v mb in
     let f1 = formula_to_condition mb mi fi f1 in
     let f2 = formula_to_condition mb mi fi f2 in
     let x_true = atomic_cond (c_is_true (e_var x Here)) in
     ternary_condition_no_simpl x_true f1 f2
  | Fite _ -> assert false (* should not happen *)
  | Fimp _ -> assert false (* should not happen *)
  | Fiff _ -> assert false (* should not happen *)
  | Fstate i ->
    let c =
      try
        Wstdlib.Mint.find i fi
      with Not_found -> assert false
    in
    List.fold_left
      (fun acc l ->
         let f = atomic_cond (lincons_to_condition mi l) in
         and_cond acc f)
      true_cond c

let rec formula_to_conditions mb mi fi acc f =
  let open B in
  match f with
  | Ftrue -> acc
  | Ffalse -> Ast.false_cond::acc
  | Fand(f1,f2) ->
     formula_to_conditions mb mi fi (formula_to_conditions mb mi fi acc f1) f2
  | Fstate i ->
    let c =
      try
        Wstdlib.Mint.find i fi
      with Not_found -> assert false
    in
    let l =
      List.fold_left
        (fun acc l ->
           let f = atomic_cond (lincons_to_condition mi l) in
           f::acc)
        [] c
    in
    List.rev_append l acc
  | _ ->
     (formula_to_condition mb mi fi f)::acc

let abstract_state_to_conditions s =
(*
  let lincons = get_lincons s in
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
*)
  let mb = invert_varmap_bool s in
  let mi = invert_varmap_int s in
  let f,fi = as_formula s in
(*
  if !Common.verbose >= 2 then
    Format.printf "@[Converting to Boolean condition @ @[@]@]@.";
 *)
  let c = formula_to_conditions mb mi fi [] f in
(*
  if !Common.verbose >= 2 then
    Format.printf "@[Converted to some Boolean condition @ @[@]@]@.";
 *)
  c
