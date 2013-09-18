open Term
open Decl
open Ident

let apply_append fn acc l =
  List.fold_left (fun l e -> fn e :: l) acc (List.rev l)

let join_and f l =
  if l = [] then [f] else
    List.map (fun f2 -> t_and f f2) l

let stop f = Slab.mem Split_goal.stop_split f.t_label

let rec collect_cases acc f =
  match f.t_node with
  | Ttrue | Tfalse | Tapp _ | Tnot _ | Tquant _ | Tlet _
  | Tbinop ((Timplies | Tiff), _ , _) -> join_and f acc
  | _ when stop f -> join_and f acc
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)
  | Tcase _ ->
      (* ??? We should split pattern matching, just as we do for Tif *)
      join_and f acc
  | Tbinop (Tor, f1, f2) ->
      List.map (t_label_copy f) (collect_cases acc f1 @ collect_cases acc f2)
  | Tbinop (Tand, f1, f2) ->
      List.map (t_label_copy f) (collect_cases (collect_cases acc f1) f2)
  | Tif (fif,fthen,felse) ->
      let acc1 = collect_cases acc fthen in
      let acc2 = collect_cases acc felse in
      join_and (t_label_copy f fif) acc1 @
      join_and (t_label_copy f (t_not fif)) acc2

let rec split f =
  match f.t_node with
  | Ttrue | Tfalse | Tapp _ | Tnot _ | Tquant (Texists, _)
  | Tbinop ( (Tand | Tor | Tiff), _, _) | Tif _ | Tcase _ -> [f]
  | _ when stop f -> [f]
  | Tvar _ | Tconst _ | Teps _ -> raise (FmlaExpected f)
  | Tquant (Tforall,fq) ->
      let vsl,trl,f1,close = t_open_quant_cb fq in
      let fn f1 = t_label_copy f (t_forall (close vsl trl f1)) in
      List.map fn (split f1)
  | Tlet (t,fb) ->
      let vs,f1,close = t_open_bound_cb fb in
      let fn f1 = t_label_copy f (t_let t (close vs f1)) in
      List.map fn (split f1)
  | Tbinop (Timplies, f1, f2) ->
      let right = split f2 in
      let cases = collect_cases [] f1 in
      List.fold_left (fun acc case ->
        List.fold_left (fun acc r ->
          t_label_copy f (t_implies case r) :: acc) acc right) [] cases

let split_goal pr f =
  let make_prop f = [create_prop_decl Pgoal pr f] in
  List.map make_prop (split f)

let split_disj = Trans.goal_l split_goal

let split_disj_name = "split_disj"

let () =
   Trans.register_transform_l split_disj_name split_disj
   ~desc:"Split disjunctions, if-then-else and case in the goal,\
   on the left hand side, and only there."
