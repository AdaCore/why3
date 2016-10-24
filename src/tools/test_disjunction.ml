open Why3
open Apron

module Base = Domain.Polyhedra

module Dom = Disjunctive_domain.Make(Base)

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
  end


let dom_eq man d d_ =
  Dom.is_leq man d d_ && Dom.is_leq man d_ d


let test1 =
  let man, env, assign, constr = init ["x"; "y"; "i"; "j"] in
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
  let man, env, assign, constr = init ["x"; "y"; "i"; "j"] in
  let d1 = constr ["x", [], 4] in
  let d2 = constr ["x", [], 3] in
  let d = Dom.join man d1 d2 in
  dom_eq man ([Base.join_list man (List.concat [d1; d2])]) d
  |> assert_ "test2"

let test3 = 
  let man, env, assign, constr = init ["x"; "y"; "i"; "j"] in
  let d1 = constr ["x", [], 4; "y", [], 3] in
  let d2 = constr ["x", [], 3; "y", [], 2] in
  let d = Dom.join man d1 d2 in
  Dom.is_leq man d (constr ["x", [1, "y"], 1])
  |> assert_ "test3"

let test4 =
  let man, env, assign, constr = init ["x"; "y"; "i"; "j"] in
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

let _ = 
  let man, env, assign, constr = init ["x"; "y"; "i"; "j"] in
  let d1 = constr ["x", [], 0; "x", [], 1] in
  Dom.print Format.err_formatter d1;
  ()
