open Term
open Decl
open Ident

let join_and f l =
  if l = [] then [f] else
    List.map (fun f2 -> t_and f f2) l

let stop f = Sattr.mem Term.stop_split f.t_attrs

let rec collect_cases acc f =
  match f.t_node with
  | Ttrue | Tfalse | Tapp _ | Tnot _ | Tquant _ | Tlet _
  | Tbinop ((Timplies | Tiff), _ , _) -> f :: acc
  | _ when stop f -> f :: acc
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)
  | Tcase _ ->
      (* ??? We should split pattern matching, just as we do for Tif *)
      f :: acc
  | Tbinop (Tor, f1, f2) ->
      let acc = collect_cases acc f1 in
      let acc = collect_cases acc f2 in
      List.map (t_attr_copy f) acc
  | Tbinop (Tand, f1, f2) ->
      let left = collect_cases [] f1 in
      let right = collect_cases [] f2 in
      List.fold_right (fun x acc ->
        List.fold_right (fun y acc ->
          t_attr_copy f (t_and x y) :: acc) right acc) left acc
  | Tif (fif,fthen,felse) ->
      let left = collect_cases [] fthen in
      let right = collect_cases[] felse in
      join_and (t_attr_copy f fif) left @
      join_and (t_attr_copy f (t_not fif)) right @ acc

let rec split f =
  match f.t_node with
  | Ttrue | Tfalse | Tapp _ | Tnot _ | Tquant (Texists, _)
  | Tbinop ( (Tand | Tor | Tiff), _, _) | Tif _ | Tcase _ -> [f]
  | _ when stop f -> [f]
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)
  | Tquant (Tforall,fq) ->
      let vsl,trl,f1,close = t_open_quant_cb fq in
      let fn f1 = t_attr_copy f (t_forall (close vsl trl f1)) in
      List.map fn (split f1)
  | Tlet (t,fb) ->
      let vs,f1,close = t_open_bound_cb fb in
      let fn f1 = t_attr_copy f (t_let t (close vs f1)) in
      List.map fn (split f1)
  | Tbinop (Timplies, f1, f2) ->
      let right = split f2 in
      let cases = collect_cases [] f1 in
      List.fold_right (fun case acc ->
        List.fold_right (fun r acc ->
         t_attr_copy f (t_implies case r) :: acc) right acc) cases []

let split_goal pr f =
  let make_prop f = [create_prop_decl Pgoal pr f] in
  List.map make_prop (split f)

let split_disj = Trans.goal_l split_goal

let split_disj_name = "split_disj"
let path_split_name = "path_split"

let () =
   Trans.register_transform_l split_disj_name split_disj
   ~desc:"Split disjunctions, if-then-else and case in the goal,\
   on the left hand side, and only there."

let () =
   Trans.register_transform_l path_split_name
    (Trans.compose_l Split_goal.split_goal_right split_disj)
   ~desc:"First do split_goal, then split_disj"
