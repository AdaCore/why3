open Why3
open Apron

module Base = Domain.Polyhedra

module Dom = Disjunctive_domain.Make(Base)

let usage_msg = Format.sprintf
  "Usage: %s"
  (Filename.basename Sys.argv.(0))

let add_opt x =
  ()

let config, _, env =
  Whyconf.Args.initialize [] add_opt usage_msg

let assert_ n b = 
  if b then 
    Format.eprintf "%s \027[32m passed\027[0m.@." n
  else
    Format.eprintf "%s \027[31m failed\027[0m.@." n

let init vars =
  let vars = List.map Var.of_string vars |> Array.of_list in
  let man = Dom.create_manager () in
  let env = Environment.make vars [||] in
  let assign = fun var_name vars const d ->
    let expr = Linexpr1.make env in
    let vars = List.map (fun (i, v) -> Coeff.s_of_int i, Var.of_string v) vars in
    Linexpr1.set_list expr vars None;
    Linexpr1.set_cst expr (Coeff.s_of_int const);
    Dom.assign_linexpr man d (Var.of_string var_name) expr None
  in
  man, env, assign, begin fun constr ->
    List.fold_left (fun d (v, vars, const) ->
        assign v vars const d) (Dom.top man env) constr
  end, begin fun d constr cst ty ->
    let expr = Linexpr1.make env in
    let constr = List.map (fun (i, v) -> Coeff.s_of_int i, Var.of_string v) constr in
    List.iter (fun (i, v) ->
                Linexpr1.set_coeff expr v i) constr;
    Linexpr1.set_cst expr (Coeff.s_of_int cst);
    let lincons = Lincons1.make expr ty in
    let lincons_a = Lincons1.array_make env 1 in
    Lincons1.array_set lincons_a 0 lincons;
    Dom.meet_lincons_array man d lincons_a
  end



let dom_eq man d d_ =
  Dom.is_leq man d d_ && Dom.is_leq man d_ d


let test1 =
  let man, env, assign, constr, _ = init ["x"; "y"; "i"; "j"] in
  let d1 = constr ["x", [], 4] in
  let d2 = constr ["y", [], 5] in
  let d1_ = match d1 with
    | [d] -> d
    | _ -> assert_ "test1" false; assert false in
  let d2_ = match d2 with
    | [d] -> d
    | _ -> assert_ "test1" false; assert false in
  let d = Dom.join man d1 d2 in
  dom_eq man [d1_; d2_] d
  |> assert_ "test1"

let test2 =
  let man, env, assign, constr, _ = init ["x"; "y"; "i"; "j"] in
  let d1 = constr ["x", [], 4] in
  let d2 = constr ["x", [], 3] in
  let d = Dom.join man d1 d2 in
  dom_eq man ([Base.join_list man (List.concat [d1; d2])]) d
  |> assert_ "test2"

let test3 = 
  let man, env, assign, constr, _ = init ["x"; "y"; "i"; "j"] in
  let d1 = constr ["x", [], 4; "y", [], 3] in
  let d2 = constr ["x", [], 3; "y", [], 2] in
  let d = Dom.join man d1 d2 in
  Dom.is_leq man d (constr ["x", [1, "y"], 1])
  |> assert_ "test3"

let test4 =
  let man, env, assign, constr,_  = init ["x"; "y"; "i"; "j"] in
  let d1 = constr ["x", [], 0; "y", [], 1] in
  let d2 = constr ["x", [], 1; "y", [], 0] in
  let d3 = constr ["x", [], 0; "y", [], 0] in
  let d4 = constr ["x", [], 1; "y", [], 1] in
  let d = Dom.join man d1 d2 in
  let d = Dom.join man d d3 in
  assert (not (dom_eq man d (constr [])));
  let d_ = Dom.join man d d4 in
  List.length d_ = 1
  |> assert_ "test4";
  let d1 = constr ["x", [], 0; "y", [], 2] in
  let d2 = constr ["x", [], 1; "y", [], 0] in
  let d3 = constr ["x", [], 0; "y", [], 0] in
  let d4 = constr ["x", [], 1; "y", [], 2] in
  let d5 = constr ["x", [], 0; "y", [], 1] in
  let d6 = constr ["x", [], 1; "y", [], 1] in
  let d = Dom.join man d1 d2 in
  let d = Dom.join man d d3 in
  assert (not (dom_eq man d (constr [])));
  let d = Dom.join man d d4 in
  let d = Dom.join man d d5 in
  let d = Dom.join man d d6 in
  List.length d = 1
  |> assert_ "test4 (2)";
  ()

let test5 =
  let man, env, assign, constr, lineq = init ["x"; "y"; "i"; "k"; "j"; "w"] in
  let d = Dom.top man env in
  let d = lineq d [1, "x"; -1, "y"] 0 Lincons1.EQ in
  let d = lineq d [1, "i"] (-8) Lincons1.EQ in
  let d = lineq d [1, "k"] (-8) Lincons1.EQ in
  let d = lineq d [-1, "w"; 1, "j"] (-1) Lincons1.SUPEQ in
  let d = lineq d [1, "w"] 0 Lincons1.SUPEQ in
  let d = lineq d [ -1, "j"] 3 Lincons1.SUPEQ in
  let d = lineq d [ 1, "j"] (-2) Lincons1.SUPEQ in
  let d = lineq d [ 1, "x"] (-10) Lincons1.SUPEQ in

  let d1 = Dom.top man env in
  let d1 = lineq d1 [1, "x"; -1, "y"] 0 Lincons1.EQ in
  let d1 = lineq d1 [1, "i"] (-8) Lincons1.EQ in
  let d1 = lineq d1 [1, "k"] (-8) Lincons1.EQ in
  let d1 = lineq d1 [ 1, "j"] (-1) Lincons1.EQ in
  let d1 = lineq d1 [ 1, "w"] 0 Lincons1.EQ in
  let d1 = lineq d1 [ 1, "x"] (-10) Lincons1.SUPEQ in

  let d = Dom.join man d d1 in

  assert_ "test5" (List.length d = 1)

let test6 =
  let man, env, assign, constr, lineq = init ["x"; "y"; "i"; "k"; "j"; "w"] in
  let d = Dom.top man env in
  let d = lineq d [1, "x"; -1, "y"] 0 Lincons1.EQ in
  let d = lineq d [1, "i"] (-8) Lincons1.SUPEQ in
  let d = lineq d [-1, "i"] 9 Lincons1.SUPEQ in

  let d1 = Dom.top man env in
  let d1 = lineq d1 [1, "x"; -1, "y"] 0 Lincons1.EQ in
  let d1 = lineq d1 [1, "i"] (-8) Lincons1.EQ in
  
  let d2 = Dom.top man env in
  let d2 = lineq d2 [1, "x"] 0 Lincons1.EQ in
  let d4 = Dom.top man env in
  let d4 = lineq d4 [1, "x"] 0 Lincons1.EQ in
  Format.printf "%d %d@." ((List.hd d2) |> Base.hash man) ((List.hd d4) |> Base.hash man);
  let d = Dom.join man d d2 in
  let d1 = Dom.join man d1 d2 in


  let d3 = Dom.join man d1 d in
  let d = Dom.widening man d1 d3 in
  assert_ "test6" (List.length d = 2)

(*
        (((((((- x) + y) = 0 /\ ((i1) - 8) = 0) /\
             ((k) - 8) = 0) /\
            0 <= (((- w1) + j) - 1)) /\ 0 <= (3 + (- j))) /\
          0 <= (j - 2)) /\ 0 <= (x - 10) }

 ((((((- x) + y) = 0 /\ ((i1) - 8) = 0) /\
     ((k) - 8) = 0) /\ (j - 1) = 0) /\
   w1 = 0) /\ 0 <= (x - 10) \/*)




(* fast *)

module Domw = Disjunctive_domain_fast.Make(Base)

let init vars =
  let vars = List.map Var.of_string vars |> Array.of_list in
  let man = Domw.create_manager () in
  let env = Environment.make vars [||] in
  let assign = fun var_name vars const d ->
    let expr = Linexpr1.make env in
    let vars = List.map (fun (i, v) -> Coeff.s_of_int i, Var.of_string v) vars in
    Linexpr1.set_list expr vars None;
    Linexpr1.set_cst expr (Coeff.s_of_int const);
    Domw.assign_linexpr man d (Var.of_string var_name) expr None
  in
  man, env, assign, begin fun constr ->
    List.fold_left (fun d (v, vars, const) ->
        assign v vars const d) (Domw.top man env) constr
  end, begin fun d constr cst ty ->
    let expr = Linexpr1.make env in
    let lincons = Lincons1.make expr ty in
    let constr = List.map (fun (i, v) -> Coeff.s_of_int i, Var.of_string v) constr in
    List.iter (fun (i, v) ->
                Linexpr1.set_coeff expr v i) constr;
    Linexpr1.set_cst expr (Coeff.s_of_int cst);
    let lincons_a = Lincons1.array_make env 1 in
    Lincons1.array_set lincons_a 0 lincons;
    Domw.meet_lincons_array man d lincons_a
  end



let dom_eq man d d_ =
  Domw.is_leq man d d_ && Domw.is_leq man d_ d

let test_w1 =
  let man, env, assign, constr, lineq = init ["x"; "y"; "z"] in
  let d1 = Domw.top man env in
  let a1 = lineq d1 [-2, "x"] (3) Lincons1.SUPEQ in
  let a2 = lineq d1 [1, "x"] (-1) Lincons1.SUPEQ in
  
  Domw.print Format.err_formatter a1;
  assert_ "testcleanup" (dom_eq man a1 a2);
  Format.eprintf "@.";
  assert_ "testcleanup" true

let test_w1 =
  let man, env, assign, constr, lineq = init ["x"; "y"; "z"] in
  let d1 = Domw.top man env in
  let a1 = lineq d1 [1, "z"] 0 Lincons1.EQ in
  let a1 = lineq a1 [1, "y"] 0 Lincons1.EQ in
  let a1 = lineq a1 [1, "x"] (-2) Lincons1.SUPEQ in
  
  let a2 = lineq d1 [1, "z"] (-4) Lincons1.EQ in
  let a2 = lineq a2 [1, "y"] (-2) Lincons1.EQ in
  let a2 = lineq a2 [1, "x"] (-2) Lincons1.SUPEQ in
  
  let a3 = lineq d1 [1, "z"] (-2) Lincons1.EQ in
  let a3 = lineq a3 [1, "y"] (-1) Lincons1.EQ in
  let a3 = lineq a3 [1, "x"] (-2) Lincons1.SUPEQ in

  let d1 = Domw.join man a1 a2 in
  let d2 = Domw.join man d1 a3 in
  Domw.print Format.err_formatter d1;
  let d3 = Domw.widening man d1 d2 in
  Domw.print Format.err_formatter d3;
  Format.eprintf "@.";
  assert_ "testw1" true

