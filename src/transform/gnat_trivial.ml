open Term

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
