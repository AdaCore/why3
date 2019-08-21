open Term
open Generic_arg_trans_utils

let rec is_trivial fml =
   (* Check wether the formula is trivial.  *)
   match fml.t_node with
   | Ttrue -> true
   | Tquant (_,tq) ->
         let _,_,t = t_open_quant tq in
         is_trivial t
   | Tlet (_,tb) ->
         let _, t = t_open_bound tb in
         is_trivial t
   | Tbinop (Timplies,_,t2) ->
         is_trivial t2
   | Tcase (_,tbl) ->
         List.for_all (fun b ->
            let _, t = t_open_branch b in
            is_trivial t) tbl
   | _ -> false

let is_trivial_trans =
  Trans.goal_l (fun _pr t ->
      if is_trivial t then
        [] (* Goal is proved *)
      else
        (* Should be equivalent to a transformation that makes no progress
           (Arg_trans is not [is_fatal]). *)
        raise (Arg_trans "Error in trivial_true"))

let () = Args_wrapper.wrap_and_register ~desc:"Prove goals whose positive part is just [true]"
    "trivial_true"
    Args_wrapper.Ttrans_l is_trivial_trans

let rec elim_t t = match t.t_node with
  | Tlet (t1,tb) ->
      let t1 = elim_t t1 in
      let v, tr = t_open_bound tb in
      begin match t1.t_node with
        | Tvar _ | Tapp (_, []) -> elim_t (t_subst (Mvs.add v t1 Mvs.empty) tr)
        | _ -> t_let_close v t1 (t_map elim_t tr)
      end
  | _ ->
      t_map elim_t t

let eliminate_trivial_let = Trans.rewrite elim_t None

let spark_simpl =
  Trans.seq_l [Trans.singleton Eliminate_epsilon.eliminate_epsilon;
               Trans.singleton Introduction.simplify_intros;
               Trans.singleton Inlining.trivial;
               Trans.singleton eliminate_trivial_let;
               Simplify_formula.simplify_formula_and_task]

let () = Args_wrapper.wrap_and_register ~desc:"Simplification transformation for SPARK-generated task"
    "spark_simpl"
    Args_wrapper.Ttrans_l spark_simpl
